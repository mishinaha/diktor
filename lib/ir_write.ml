(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第18章 精緻化木から KIR への書き出し

   本章は、型検査を済ませた単位の並び(第16章の `type_check_files` の結果)を、
   第17章の `Ir.program` に変換する。
   仕様は親リポジトリの `doc/IRSpec.md` が定める。
   KIR は別の処理系(RustKeleut)も読み、その処理系のフロントエンドも同じ KIR を書く。
   そのため、本章の変換規則を Diktor の都合で決めることはできない。
   名前の付け方、スロットとキャプチャの番号、表の順序は、どれも IRSpec が定める規則に従う。

   第14章の評価器は、木をたどりながら次のものをその場で決める。
   本章は、同じものを書き出す時点で決め、KIR に書く。

   | 評価器がその場で決めるもの | KIR での書き方 |
   |---|---|
   | ローカルの名前を引く表 | 関数ごとのスロットの番号 |
   | クロージャがキャプチャする環境の全体 | 関数ごとのキャプチャの並び |
   | 末尾位置と、操作節の背骨(§18.5) | `call`、`handle`、`resume` の印と、操作節の分類 |
   | インスタンスの対象の型、メソッドの辞書の位置 | 辞書の式とインスタンス表 |
   | 数値リテラルの値 | 値を確定させたリテラルか、範囲外のリテラル |
   | トップレベルの宣言を指すキー | 単位のキーと修飾名からなるシンボル |

   書き出しは 2 段階で行う。
   第 1 段階は、すべての単位の宣言をたどって、型、エフェクト、クラス、インスタンス、
   グローバルのシンボルを決め、単位ごとの初期化手順を作る(表は §18.3、処理は §18.12)。
   第 2 段階は、初期化手順ごとにルート関数の本体を書き出す(§18.5 から §18.11)。
   段階を分けるのは、本体が、まだ宣言していないグローバルやインスタンスを参照することがあるからである。
   前方参照も、インスタンスを宣言より前で使うことも、型検査に通る。

   書き出しは決定的でなければならない。
   本章は、ハッシュ表をキーで引くことにだけ使い、ハッシュ表を走査する順を出力に使わない。
   表の項目の順序はどれも、宣言の順か、IRSpec が定める固定の順である。 *)
open Aux
open Syntax
module T = Tree.Tree
module I = Ir
module SMap = Map.Make (String)

(* ## 18.1 入力

   書き出しが受け取るのは、単位ごとのキー、元のファイルのパスの並び(IRSpec 2.3 節の `paths`)、
   平坦化と型検査を済ませた宣言の並びである。
   単位は、プレリュード、import した単位(初期化の順)、起点の順に並べる。
   import した単位のキーと表示用のパスは、第16章が import の文から決める(IRSpec 2.2 節、2.3 節)。
   プレリュードと起点のキーは固定で、パスはコマンド行から決まる。
   組み込みの単位はここに含めず、本章が追加する。 *)
type unit_src = { us_key : string; us_paths : string list; us_decls : T.decl list }

(* ## 18.2 組み込みの表

   組み込みの型、クラス、値は、プログラムによらず同じ表を同じ順で書く(IRSpec 付録 A)。
   組み込みのクラスのメソッドは、どれもメソッド自身の辞書を持たない。
   予約述語(`Integral` と `Fractional`)は辞書の引数にならないので、クラス表に書かない。 *)
let builtin_types = [ "Boolean"; "Int32"; "Int64"; "Float64"; "String"; "Never"; "Ref"; "Array"; "MutableArray" ]

let builtin_classes =
  [
    ("Add", [ "add" ]);
    ("Sub", [ "sub" ]);
    ("Mul", [ "mul" ]);
    ("Div", [ "div" ]);
    ("Rem", [ "rem" ]);
    ("Neg", [ "neg" ]);
    ("Eq", [ "eq" ]);
    ("Ord", [ "lt"; "le"; "gt"; "ge" ]);
    ("Show", [ "show" ]);
  ]

let builtin_values =
  [
    "Ref.new";
    "Ref.get";
    "Ref.set";
    "Array.length";
    "Array.get";
    "Array.each";
    "MutableArray.new";
    "MutableArray.length";
    "MutableArray.get";
    "MutableArray.set";
    "MutableArray.freeze";
    "pinned";
  ]

(* ## 18.3 シンボルの表

   シンボルは `単位の鍵/修飾名` の形式である(IRSpec 3 節)。
   `単位の鍵` は IRSpec と診断メッセージの表記で、単位のキーを指す。
   第6章は、起点でない単位の型やエフェクトの名前を、接頭辞 `%N.` を付けた内部名で持つ。
   `N` は Diktor のプロセスの中での単位の番号なので、シンボルには書かない。
   修飾名には、`Type.display` で内部名から接頭辞を取り除いた名前を使う。

   型、エフェクト、クラスのシンボルは、名前の oid から引く。
   oid は第1章のインターン表の番号で、同じ名前なら同じ oid になる。
   接頭辞を付けた内部名は単位ごとに異なるので、その oid からは単位が決まる。
   しかし、接頭辞のない名前は、プレリュードのものか起点のものかを名前からは決められない。
   そこで、接頭辞から単位を推測することはせず、宣言をたどって表を作る。

   グローバルのシンボルは、第5章の木が参照先の宣言を表すのに使うキー
   (束縛ノードの oid と束縛した名前の組)から引く。
   同じ単位で同じ修飾名を再び束縛したときは、2 つ目から `#1`、`#2` を付ける。 *)
type tables = {
  types : (oid, string) Hashtbl.t;
  effects : (oid, string) Hashtbl.t;
  classes : (oid, string) Hashtbl.t;
  instances : (oid * oid, string) Hashtbl.t;
  globals : (oid * string, string) Hashtbl.t;
}

let new_tables () =
  {
    types = Hashtbl.create 64;
    effects = Hashtbl.create 16;
    classes = Hashtbl.create 16;
    instances = Hashtbl.create 64;
    globals = Hashtbl.create 256;
  }

let find_sym what tbl k = match Hashtbl.find_opt tbl k with Some s -> s | None -> bug ("KIR の書き出し: 記号がありません: " ^ what)

let type_sym tb c = find_sym ("型 " ^ Type.name_of c) tb.types c

let effect_sym tb e = find_sym ("エフェクト " ^ Type.name_of e) tb.effects e

let class_sym tb c = find_sym ("クラス " ^ Type.name_of c) tb.classes c

(* シンボルの名前の部分を返す。シンボルの最後の `/` より後ろである *)
let sym_name s = match String.rindex_opt s '/' with Some i -> String.sub s (i + 1) (String.length s - i - 1) | None -> s

(* 名前を最後の `.` で 2 つに分ける。`Cls.m` のメソッドと `Eff.op` の操作の名前は `.` を含まないので、
   module の修飾と単位の接頭辞は前の部分にだけ残る *)
let split_last_dot s =
  match String.rindex_opt s '.' with
  | Some i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))
  | None -> bug ("KIR の書き出し: 修飾名ではありません: " ^ s)

(* ## 18.4 Rep と yield の印

   Rep は型から決める(IRSpec 4 節)。
   `Type.repr` で `Link` の連鎖をたどった結果が、引数のない組み込みの 5 つの型
   (`Boolean`、`Int32`、`Int64`、`Float64`、`String`)のどれかならその型の Rep で、
   それ以外は `any` である。
   ノードに型が書かれていない場合(型検査が型を書かない種類のノード)も `any` にする。

   `noyield` を付けるのは、エフェクト行が次の条件を満たす関数の型である。
   行が閉じていて、行のラベルがすべて、プレリュードの `Console`、組み込みの `Heap`、
   組み込みの `Blocking` のどれかである。
   型変数で終わる行は開いているので `yield` になる。
   ラベルは oid で比較する。
   `--no-prelude` のときに起点が宣言した `Console` はユーザが処理できるので、ここに含めない。 *)
let rep_of_ty t =
  match Type.repr t with
  | Type.TCon (c, []) -> (
      match Type.name_of c with
      | "Boolean" -> I.RBool
      | "Int32" -> I.RI32
      | "Int64" -> I.RI64
      | "Float64" -> I.RF64
      | "String" -> I.RStr
      | _ -> I.RAny)
  | _ -> I.RAny

let ty_opt (d, _) = d.Tree.ElabData.ty_field

let rep_of_node n = match ty_opt n with Some t -> rep_of_ty t | None -> I.RAny

(* 束縛が名前として持つパターンの Rep を返す。
   トップレベルの値束縛では、型検査がこのパターンに型を書かないので、束縛のノードの型を使う *)
let rep_of_name name (bnode : T.let_binding) = match ty_opt name with Some t -> rep_of_ty t | None -> rep_of_node bnode

let noyield tb t =
  let allowed l = l = Type.eff_heap || l = Type.eff_blocking || Hashtbl.find_opt tb.effects l = Some "prelude/Console" in
  let rec row r = match Type.repr r with Type.TRowEmpty -> true | Type.TRowExtend (l, _, rest) -> allowed l && row rest | _ -> false in
  match Type.repr t with Type.TArrow (_, _, eff) -> row eff | _ -> false

let yield_of_node tb n = match ty_opt n with Some t -> not (noyield tb t) | None -> true

(* 辞書パラメータのキーを返す。第14章の `dict_params_of` と同じく、
   インスタンスのメソッドの束縛では、
   実装の型の辞書パラメータ(`DMethod` の 1 つ目)を使う *)
let dict_params_of node = match Tree.get_dict node with Tree.DAbs ks | Tree.DMethod (ks, _, _) -> ks | _ -> []

let rec strip_annot ((_, p) as node : T.pat) = match p with T.PAnnot (q, _) -> strip_annot q | _ -> node

(* ## 18.5 書き出し中の関数、スロット、キャプチャ

   書き出している途中の関数を `frame` で表し、以下では**書き出し中の関数**と呼ぶ。
   書き出し中の関数は、スロットの個数と Rep、キャプチャの並び、親の関数を持つ。
   親の関数は、その関数の生成箇所(§18.10)を本体に持つ関数である。
   スロットの番号は、まず引数に 0 から振り、続けて、
   束縛する箇所にたどり着いた順に振る(IRSpec 6.4 節)。
   本章は木を正準なテキストの順にたどるので、たどり着いた順に振れば規則どおりの番号になる。
   そのため、式の子を書き出す順は、テキストに子が現れる順と一致させる。
   OCaml は、組やレコードの要素とコンストラクタの引数を評価する順を規定していないので、
   子を 2 つ以上書き出す箇所では `let` で順を固定する。

   名前の環境は、名前から、その名前を束縛した関数と、その関数での読み方の組を引く。
   読み方は、スロット、キャプチャ、辞書の引数のどれを何番で読むかを表す(`Ir.var`)。
   現在の関数より外側の関数が束縛した名前を読むときは、
   間にある関数を 1 つずつたどってキャプチャを追加する(`access`)。
   たとえば、内側のクロージャが 2 つ外側の関数の変数を読むと、
   間のクロージャもその変数をキャプチャする。
   キャプチャの並びは、親の関数での読み方の順である。
   辞書の引数、キャプチャ、スロットの順に並べ、それぞれの中では番号の昇順にする。
   ところが、親の関数でのキャプチャの番号は、親の関数のキャプチャの並びが決まるまで決まらない。
   そこで、書き出している間はキャプチャを仮の番号(関数をまたいで一意な整数)で表しておく。
   ルート関数を書き終えてから、外側の関数から順に並びを決め、
   仮の番号を確定した番号に置き換える(§18.11)。

   操作節の関数は、自分の継続を再開する `resume` のうち、背骨の外にあるものの個数を数える。
   背骨は、操作節の本体から末尾位置だけをたどった経路である。
   ハンドラの本体の関数の中の `resume` は、その本体を囲む操作節の継続を再開する。
   そのため、本体の関数は、囲んでいる関数から `resume` の持ち主をそのまま引き継ぐ。
   持ち主は、その `resume` が再開する継続を受け取る操作節である。 *)
type frame = {
  fr_root : root;
  fr_parent : frame option;
  fr_sym : string;
  fr_kind : I.fn_kind;
  fr_params : I.rep list;
  mutable fr_nslots : int;
  mutable fr_locals : I.rep list; (* 引数より後のスロットの Rep。振った順の逆に並ぶ *)
  mutable fr_caps : (int * I.var) list; (* 仮の番号と、親の関数での読み方。追加した順 *)
  mutable fr_owner : frame option; (* resume の持ち主である操作節の関数 *)
  mutable fr_ntail_resumes : int;
  mutable fr_subst : (int * int) list; (* 仮の番号から、確定したキャプチャの番号への対応 *)
  mutable fr_final_caps : I.var list;
  mutable fr_cap_reps : I.rep list;
}

(* ルート関数ごとの状態。生成箇所に次に振る番号、作った frame(作った順の逆)、書き終えた関数を持つ *)
and root = {
  r_sym : string;
  mutable r_sites : int;
  mutable r_frames : frame list;
  mutable r_fns : ((int * int) * frame * pending) list;
}

and pending = { pd_yield : bool; pd_dicts : int; pd_result : I.rep; pd_pats : I.pat list; pd_guard : I.exp option; pd_body : I.exp }

type binding = { b_frame : frame; b_var : I.var }

module DK = Map.Make (struct
  type t = oid * oid

  let compare = compare
end)

type genv = {
  tb : tables;
  fr : frame;
  names : binding SMap.t;
  dkeys : binding DK.t;
  tail : bool; (* 末尾位置にあれば真 *)
  spine : bool; (* 操作節の背骨の上にあれば真 *)
}

let provisional = ref 0

let new_frame ?parent ~root ~sym ~kind ~params ~owner () =
  let fr =
    {
      fr_root = root;
      fr_parent = parent;
      fr_sym = sym;
      fr_kind = kind;
      fr_params = params;
      fr_nslots = List.length params;
      fr_locals = [];
      fr_caps = [];
      fr_owner = owner;
      fr_ntail_resumes = 0;
      fr_subst = [];
      fr_final_caps = [];
      fr_cap_reps = [];
    }
  in
  root.r_frames <- fr :: root.r_frames;
  fr

let new_slot fr rep =
  let i = fr.fr_nslots in
  fr.fr_nslots <- i + 1;
  fr.fr_locals <- rep :: fr.fr_locals;
  i

(* 関数 fr から束縛 b を読む方法を返す。b の関数が fr の外側にあれば、
   間にある関数にキャプチャを追加する *)
let rec access fr b =
  if fr == b.b_frame then b.b_var
  else
    match fr.fr_parent with
    | None -> bug ("KIR の書き出し: 根の関数の外の変数を読もうとしました: " ^ fr.fr_sym)
    | Some p -> (
        let pv = access p b in
        match List.find_opt (fun (_, v) -> v = pv) fr.fr_caps with
        | Some (id, _) -> I.VEnv id
        | None ->
            incr provisional;
            let id = !provisional in
            fr.fr_caps <- fr.fr_caps @ [ (id, pv) ];
            I.VEnv id)

let bind_name env x var = { env with names = SMap.add x { b_frame = env.fr; b_var = var } env.names }

let bind_dkeys env ks first = { env with dkeys = snd (List.fold_left (fun (i, m) k -> (i + 1, DK.add k { b_frame = env.fr; b_var = I.VDParam i } m)) (first, env.dkeys) ks) }

(* 末尾位置になく、背骨の外にある子の環境を返す。末尾位置を引き継ぐ子には env をそのまま渡す *)
let nt env = { env with tail = false; spine = false }

(* 生成箇所に番号を振る。番号はルート関数ごとに 0 から数える *)
let next_site env =
  let r = env.fr.fr_root in
  let n = r.r_sites in
  r.r_sites <- n + 1;
  n

let finish fr ~order pd = fr.fr_root.r_fns <- (order, fr, pd) :: fr.fr_root.r_fns

(* ## 18.6 リテラル

   数値リテラルは、ノードの型の先頭の型構成子(`Int32`、`Int64`、`Float64`)に合わせて読み、
   値を確定させる。
   読むのに使う関数は第14章の `number_value` と同じ(`Int32.of_string`、`Int64.of_string`、
   `float_of_string`)である。
   読めなければ範囲外のリテラルにする。
   範囲外のリテラルは評価したときに初めて実行時エラーになるので、
   型検査の段階でエラーにしてはならない。
   範囲外のリテラルには、第2章の `show_number` が返す表記を持たせ、診断に使う。

   パターンの数値は、パターンのノードの型に合わせて読む。
   型検査が範囲を検査しているので、パターンの数値が読めないことはない。 *)
let number_head n = match ty_opt n with Some t -> ( match Type.repr t with Type.TCon (c, _) -> Type.name_of c | _ -> "") | None -> ""

let number_lit node (num : number) =
  match number_head node with
  | "Int32" -> ( match Int32.of_string num.n_text with v -> I.Lit (I.LI32 v) | exception Failure _ -> I.Lit_error (I.Lit_range, Lexer.show_number num))
  | "Int64" -> ( match Int64.of_string num.n_text with v -> I.Lit (I.LI64 v) | exception Failure _ -> I.Lit_error (I.Lit_range, Lexer.show_number num))
  | "Float64" -> (
      match float_of_string num.n_text with
      | v -> I.Lit (I.LF64 (Int64.bits_of_float v))
      | exception Failure _ -> I.Lit_error (I.Lit_range, Lexer.show_number num))
  | h -> bug ("KIR の書き出し: 数値リテラルの型が不正です: " ^ h)

let pattern_number node (num : number) =
  match number_lit node num with I.Lit l -> l | _ -> bug ("KIR の書き出し: パターンの数値が範囲外です: " ^ Lexer.show_number num)

(* ## 18.7 パターン

   パターンは 6 種に変換する。
   型注釈は取り除く。
   レコードのパターンの末尾は、`None`(タプル)を `closed`、`Some _`(ワイルドカード)を `open`、
   それ以外を `rest` にする。
   コンストラクタのパターンは、パターンを書いたフィールドだけを、フィールドの位置の昇順に並べる。
   第14章の照合も同じ順にフィールドをたどる。

   変数のパターンにたどり着いたら、引数 `bind` の関数を呼んで番号を決める。
   関数の中のパターンではスロットを振り、
   `def_pattern` のパターンではグローバルの並びの中の番号を振る。
   パターンをたどる処理を 1 つの関数で共有するので、2 つの番号の振り方が食い違わない。 *)
let rec pat ~bind tb ((_, p) as node : T.pat) : I.pat =
  match p with
  | T.PWildcard -> I.PWild
  | T.PVar x -> I.PBind (bind x node)
  | T.PAnnot (q, _) -> pat ~bind tb q
  | T.PBool b -> I.PLit (I.LBool b)
  | T.PText s -> I.PLit (I.LStr s)
  | T.PNumber n -> I.PLit (pattern_number node n)
  | T.PVariant (l, q) -> I.PVariant (l, pat ~bind tb q)
  | T.PRecord (fs, tl) ->
      let fields = List.map (fun (l, q) -> (l, pat ~bind tb q)) fs in
      let tail =
        match tl with
        | None -> I.Closed
        | Some (_, T.PWildcard) -> I.Open
        | Some q -> I.Rest (pat ~bind tb q)
      in
      I.PRecord (fields, tail)
  | T.PCtor (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtorPat (data, ctor, f2a)) ->
          let fields =
            List.concat
              (List.mapi
                 (fun fi a -> match a with Some ai -> [ (fi, pat ~bind tb (List.nth args ai).T.cap_pat) ] | None -> [])
                 (Array.to_list f2a))
          in
          I.PCtor (type_sym tb data, Type.display (Type.name_of ctor), fields)
      | _ -> bug "KIR の書き出し: PCtor が解決されていません")

(* 関数の中のパターン。変数ごとにスロットを振り、名前を環境に追加する *)
let local_pat env p =
  let binds = ref [] in
  let ip =
    pat env.tb p ~bind:(fun x node ->
        let i = new_slot env.fr (rep_of_node node) in
        binds := (x, i) :: !binds;
        i)
  in
  (ip, List.fold_left (fun env (x, i) -> bind_name env x (I.VLocal i)) env (List.rev !binds))

(* ## 18.8 辞書

   辞書の式は、第5章の証拠(evidence。どのインスタンスの辞書を使うかを表す項)の穴を、
   その解に置き換えたものである。
   穴は、解(`h_sol`)をたどり終えてから書く。
   未解決の穴は対話的な実行の表示にだけ現れ、ファイルの書き出しには現れない。

   `EvInst` は、ユーザが宣言したインスタンスなら `dinst` に、
   それ以外は組み込みのインスタンス `dbuiltin` に変換する。
   第14章の `select_method` も、ユーザのインスタンス表を先に引き、なければ組み込みの表を引く。
   組み込みと同じクラスと型構成子の組に対するユーザの宣言は型検査が拒否するので、
   2 つの表は重ならない。 *)
let rec dict env (ev : Tree.evidence) : I.dict =
  match ev with
  | Tree.EvParam k -> (
      match DK.find_opt k env.dkeys with
      | Some b -> I.DVar (access env.fr b)
      | None -> bug "KIR の書き出し: 辞書パラメータが束縛されていません")
  | Tree.EvInst (c, n, ps) -> (
      match Hashtbl.find_opt env.tb.instances (c, n) with
      | Some i -> I.DInst (i, List.map (dict env) ps)
      | None -> I.DBuiltin (class_sym env.tb c, type_sym env.tb n))
  | Tree.EvRecord fs -> I.DRecord (List.map (fun (l, e) -> (Type.name_of l, dict env e)) fs)
  | Tree.EvVariant fs -> I.DVariant (List.map (fun (l, e) -> (Type.name_of l, dict env e)) fs)
  | Tree.EvHole { Tree.h_sol = Some e; _ } -> dict env e
  | Tree.EvHole _ -> bug "KIR の書き出し: 解かれていない辞書の穴があります"

let use_dicts env node = match Tree.get_dict node with Tree.DUse hs -> List.map (fun h -> dict env (Tree.EvHole h)) hs | _ -> []

let with_dicts env node e = match use_dicts env node with [] -> e | ds -> I.Dictapp (e, ds)

let op_dict env node = match Tree.get_dict node with Tree.DUse [ h ] -> dict env (Tree.EvHole h) | _ -> bug "KIR の書き出し: 演算子に証拠がありません"

(* クラスのメソッドの参照。使う位置の辞書の並びのうち、
   クラスパラメータの制約の位置にある辞書を `d` にし、
   残りを順に `o…` にする。位置は第14章の `method_selector` と同じく、
   型スキームの制約を正準順に並べた中で求める *)
let method_ref env node q =
  let cls_name, m = split_last_dot q in
  let ci = match Decls.find_class (Type.intern cls_name) with Some ci -> ci | None -> bug ("KIR の書き出し: クラスがありません: " ^ cls_name) in
  let scheme = match List.assoc_opt m ci.Decls.ci_methods with Some s -> s | None -> bug ("KIR の書き出し: メソッドがありません: " ^ q) in
  let cs = Unify.constraints_of scheme in
  let rec index j = function
    | [] -> bug ("KIR の書き出し: メソッドの型にクラスの引数がありません: " ^ q)
    | ((i : Type.var_info), c) :: rest -> if i.Type.vid = ci.Decls.ci_param.Type.vid && c = ci.Decls.ci_name then j else index (j + 1) rest
  in
  let idx = index 0 cs in
  let ds = use_dicts env node in
  if List.length ds <> List.length cs then bug ("KIR の書き出し: メソッドの辞書の数が合いません: " ^ q);
  let d = List.nth ds idx in
  let own = List.filteri (fun j _ -> j <> idx) ds in
  I.Method (class_sym env.tb ci.Decls.ci_name, m, d, own)

(* 呼び出しと perform の引数を返す。引数は `_item` のレコードの式で、
   最も外側の要素が先頭の引数である *)
let rec args_of ((_, e) : T.exp) =
  match e with
  | T.RecordExtend (rest, _, v) -> v :: args_of rest
  | T.RecordEmpty -> []
  | _ -> bug "KIR の書き出し: 引数がレコードの式ではありません"

(* ## 18.9 式

   式の変換規則は IRSpec 5.5 節の表のとおりである。
   ここでは、表に現れない 3 つの点を述べる。

   - 名前は、ローカルの環境、トップレベルの宣言(`RVar`)、
     引数のないコンストラクタ(`RCtor`)の順に引く。
     第14章の `Ident` と同じ順である。
   - 末尾位置と背骨は、環境の `tail` と `spine` で子に伝える。
     `let`、`letpat`、`letrec` の本体の式、`seq` の最後の式、`match` の節の本体、
     `&&` と `||` の右辺だけが親の値を引き継ぎ、
     それ以外の子ではどちらも偽になる(IRSpec 5.3 節)。
     木の `Run` は KIR のノードを作らないので、その本体には環境をそのまま渡す。
   - 背骨の外の `resume` を書いたら、その `resume` の持ち主である操作節の関数のカウンタに 1 を足す。
     操作節の分類(§18.10)は、このカウンタが 0 かどうかで T と G を区別する。 *)
let rec exp env ((_, e) as node : T.exp) : I.exp =
  match e with
  | T.Bool b -> I.Lit (I.LBool b)
  | T.Text s -> I.Lit (I.LStr s)
  | T.Number n -> number_lit node n
  | T.Hole -> I.Hole
  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.names with
      | Some b ->
          let v = match access env.fr b with I.VLocal i -> I.Local i | I.VEnv i -> I.Env i | I.VDParam _ -> bug "KIR の書き出し: 名前が辞書を指しています" in
          with_dicts env node v
      | None -> (
          match Tree.get_resolved node with
          | Some (Tree.RVar (Tree.GDecl (oid, x))) -> with_dicts env node (I.Global (find_sym ("大域 " ^ x) env.tb.globals (oid, x)))
          | Some (Tree.RVar (Tree.GBuiltin x)) -> with_dicts env node (I.Global ("builtin/" ^ x))
          | Some (Tree.RVar (Tree.GMethod q)) -> method_ref env node q
          | Some (Tree.RCtor (data, c, _)) -> I.Construct (type_sym env.tb data, Type.display (Type.name_of c), [])
          | _ -> bug ("KIR の書き出し: Ident が解決されていません: " ^ name)))
  | T.Apply (f, arg) ->
      let fe = exp (nt env) f in
      let args = List.map (exp (nt env)) (args_of arg) in
      I.Call { I.c_tail = env.tail; c_yield = yield_of_node env.tb f; c_fn = fe; c_args = args }
  | T.Construct (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtor (data, c, a2f)) ->
          let fields = List.mapi (fun ai (a : T.ctor_arg) -> (a2f.(ai), exp (nt env) a.T.ca_exp)) args in
          I.Construct (type_sym env.tb data, Type.display (Type.name_of c), fields)
      | _ -> bug "KIR の書き出し: Construct が解決されていません")
  | T.Variant (l, v) -> I.Variant (l, exp (nt env) v)
  | T.BinOp (l, op, r) -> (
      match Prims.bin_op_sem op with
      | Prims.OpBool ->
          let le = exp (nt env) l in
          let re = exp env r in
          if op = And then I.And (le, re) else I.Or (le, re)
      | Prims.OpMethod (cls, m) ->
          let d = op_dict env node in
          let le = exp (nt env) l in
          let re = exp (nt env) r in
          I.Opcall ("builtin/" ^ cls, m, d, [ le; re ])
      | Prims.OpMethodNot (cls, m) ->
          let d = op_dict env node in
          let le = exp (nt env) l in
          let re = exp (nt env) r in
          I.Not (I.Opcall ("builtin/" ^ cls, m, d, [ le; re ])))
  | T.Not v -> I.Not (exp (nt env) v)
  | T.Neg v ->
      let cls, m = Prims.neg_method in
      let d = op_dict env node in
      I.Opcall ("builtin/" ^ cls, m, d, [ exp (nt env) v ])
  | T.Lambda { l_params; l_body } -> lambda_site env ~params:l_params ~body:l_body ~fn_node:(fst node, ())
  | T.Let (b, rest) -> let_exp env b rest
  | T.LetRec (bs, rest) ->
      let env', items = rec_group env bs in
      let body = exp env' rest in
      I.Letrec (items, body)
  | T.Seq [] -> I.Rec_empty
  | T.Seq [ x ] -> exp env x
  | T.Seq es ->
      let rec go = function [] -> [] | [ last ] -> [ exp env last ] | x :: rest -> let v = exp (nt env) x in v :: go rest in
      I.Seq (go es)
  | T.Match (scrut, clauses) ->
      let s = exp (nt env) scrut in
      let cls =
        List.map
          (fun ((_, c) : T.clause) ->
            let p, env2 = local_pat env c.T.cl_pat in
            let g = Option.map (exp (nt env2)) c.T.cl_guard in
            let body = exp env2 c.T.cl_body in
            { I.cl_pat = p; cl_guard = g; cl_body = body })
          clauses
      in
      I.Match (s, cls)
  | T.RecordEmpty -> I.Rec_empty
  | T.RecordExtend (rest, l, v) ->
      let ve = exp (nt env) v in
      let re = exp (nt env) rest in
      I.Rec_extend (l, ve, re)
  | T.RecordUpdate (r, l, v) ->
      let re = exp (nt env) r in
      let ve = exp (nt env) v in
      I.Rec_update (l, re, ve)
  | T.RecordRestriction (r, l) -> I.Rec_restrict (l, exp (nt env) r)
  | T.RecordSelection (r, l) -> I.Rec_select (l, exp (nt env) r)
  | T.Perform (_, arg) -> (
      match Tree.get_resolved node with
      | Some (Tree.ROp op) ->
          let eff, o = split_last_dot (Type.name_of op) in
          I.Perform (effect_sym env.tb (Type.intern eff), o, List.map (exp (nt env)) (args_of arg))
      | _ -> bug "KIR の書き出し: Perform が解決されていません")
  | T.Handle (body, clauses) -> handle_site env body clauses
  | T.Resume arg ->
      let v = match arg with Some a -> exp (nt env) a | None -> I.Rec_empty in
      if not env.spine then (
        match env.fr.fr_owner with
        | Some o -> o.fr_ntail_resumes <- o.fr_ntail_resumes + 1
        | None -> bug "KIR の書き出し: 操作節の外に resume があります");
      I.Resume (env.spine, v)
  | T.Run (_, b) -> exp env b

(* 束縛の値を書く。辞書を受け取る束縛は `dictabs` の生成箇所にし、
   その本体を関数の定義のクロージャか初期化式にする。
   関数の定義は `closure` の生成箇所にする。値の束縛は、その場に初期化式を書く *)
and binding_value env ((_, b) as bnode : T.let_binding) =
  let plain env =
    match b.T.lb_params with
    | Some ps -> lambda_site env ~params:ps ~body:b.T.lb_body ~fn_node:(fst bnode, ())
    | None -> exp (nt env) b.T.lb_body
  in
  match dict_params_of bnode with
  | [] -> plain env
  | ks ->
      let result = match b.T.lb_params with Some _ -> I.RAny | None -> rep_of_node b.T.lb_body in
      dictabs_site env ks ~result (fun env -> plain env)

and is_closure_binding ((_, b) as bnode : T.let_binding) = b.T.lb_params <> None || dict_params_of bnode <> []

and let_exp env ((_, b) as bnode : T.let_binding) rest =
  let name = strip_annot b.T.lb_name in
  match snd name with
  | T.PVar x ->
      let rep = if is_closure_binding bnode then I.RAny else rep_of_name name bnode in
      let n = new_slot env.fr rep in
      let v = binding_value env bnode in
      let body = exp (bind_name env x (I.VLocal n)) rest in
      I.Let (n, v, body)
  | _ ->
      let p, env2 = local_pat env b.T.lb_name in
      let v = binding_value env bnode in
      let body = exp env2 rest in
      I.Letpat (p, v, body)

(* let rec のグループ。グループの名前に先にスロットを振ってから、各項目を書く。
   項目の式はどれも別の関数の生成箇所なので、現在の関数のスロットを振らない。
   そのため、名前のスロットを先にまとめて振っても、テキストの順に振った番号と一致する *)
and rec_group env (bs : T.let_binding list) =
  let names =
    List.map
      (fun ((_, b) : T.let_binding) ->
        match snd (strip_annot b.T.lb_name) with T.PVar x -> x | _ -> bug "KIR の書き出し: let rec の名前が変数ではありません")
      bs
  in
  let slots = List.map (fun _ -> new_slot env.fr I.RAny) names in
  let env' = List.fold_left2 (fun env x n -> bind_name env x (I.VLocal n)) env names slots in
  let items =
    List.map2
      (fun n (((_, b) as bnode) : T.let_binding) ->
        let ps, body, fn_node =
          match b.T.lb_params with
          | Some ps -> (ps, b.T.lb_body, (fst bnode, ()))
          | None -> (
              match snd b.T.lb_body with
              | T.Lambda { l_params; l_body } -> (l_params, l_body, (fst b.T.lb_body, ()))
              | _ -> bug "KIR の書き出し: let rec の右辺が関数ではありません")
        in
        let site env = lambda_site env ~params:ps ~body ~fn_node in
        let e = match dict_params_of bnode with [] -> site env' | ks -> dictabs_site env' ks ~result:I.RAny site in
        (n, e))
      slots bs
  in
  (env', items)

(* ## 18.10 持ち上げた関数の生成箇所

   持ち上げた関数(ラムダリフティングで取り出した関数)を作る式は、
   `closure`、`dictabs`、`handle` の 3 種である。
   この 3 種の式を生成箇所と呼ぶ。
   生成箇所にたどり着いたら番号を振り、作る関数の内容をすぐに書き出す。
   書き出しは木を正準なテキストの順にたどるので、番号は前順になる(IRSpec 3.4 節)。

   `closure` の生成箇所が作る関数は種類が `lambda` で、仮引数を 0 から始まるスロットで受け取る。
   変数の仮引数はそのスロットをそのまま使い、`_` は何もせず、
   それ以外のパターンは本体を `letpat` で囲む。
   `letpat` は、最初の仮引数のものが最も外側になるように重ねる。
   パターンのスロットを本体より先に振るので、番号はテキストの順と一致する。
   この関数の本体は末尾位置にあり、背骨の外にある。 *)
and lambda_site env ~params ~body ~fn_node =
  let n = next_site env in
  let sym = env.fr.fr_root.r_sym ^ "$" ^ string_of_int n in
  let fr = new_frame ~parent:env.fr ~root:env.fr.fr_root ~sym ~kind:I.Lambda ~params:(List.map rep_of_node params) ~owner:None () in
  let env0 = { env with fr; tail = true; spine = false } in
  let b = lambda_body env0 params body in
  finish fr ~order:(n, 0) { pd_yield = yield_of_node env.tb fn_node; pd_dicts = 0; pd_result = rep_of_node body; pd_pats = []; pd_guard = None; pd_body = b };
  I.Closure (sym, [])

(* 仮引数のパターンを変換し、本体を書く。lambda と retclause の関数が共有する *)
and lambda_body env params body =
  let env, wraps =
    List.fold_left
      (fun (env, wraps) (j, p) ->
        let q = strip_annot p in
        match snd q with
        | T.PVar x -> (bind_name env x (I.VLocal j), wraps)
        | T.PWildcard -> (env, wraps)
        | _ ->
            let ip, env' = local_pat env p in
            (env', (ip, j) :: wraps))
      (env, [])
      (List.mapi (fun j p -> (j, p)) params)
  in
  let b = exp env body in
  List.fold_left (fun inner (ip, j) -> I.Letpat (ip, I.Local j, inner)) b wraps

(* 辞書を受け取る関数の生成箇所。本体は末尾位置になく、背骨の外にある *)
and dictabs_site env ks ~result mk_body =
  let n = next_site env in
  let sym = env.fr.fr_root.r_sym ^ "$" ^ string_of_int n in
  let fr = new_frame ~parent:env.fr ~root:env.fr.fr_root ~sym ~kind:I.Dictabs_fn ~params:[] ~owner:None () in
  let env0 = bind_dkeys { env with fr; tail = false; spine = false } ks 0 in
  let b = mk_body env0 in
  finish fr ~order:(n, 0) { pd_yield = true; pd_dicts = List.length ks; pd_result = result; pd_pats = []; pd_guard = None; pd_body = b };
  I.Dictabs (sym, [])

(* ハンドラ式の生成箇所。本体、操作節(書いた順)、return 節、cancel 節の順に関数を作る。

   操作節の関数は、操作の引数をスロット 0 から受け取る。
   引数のパターンは `pats` のフィールドに書く。
   変数のパターンは、引数のスロットをそのまま使うので `(wild)` と書く。
   節の分類は、返り値の型が `Never` の操作(`RNeverOp`)の節なら N、
   本体を書き終えた時点で背骨の外の `resume` が 0 個なら T、それ以外は G である(IRSpec 9.2 節)。
   N の節と return 節の本体は、ハンドラ式が末尾位置にあるときだけ末尾位置にある(IRSpec 5.3 節)。
   T と G の節の本体は末尾位置になく、背骨はこの本体から始まる。
   ガードは背骨の外にある。 *)
and handle_site env body clauses =
  let n = next_site env in
  let r = env.fr.fr_root in
  let base = r.r_sym ^ "$h" ^ string_of_int n in
  let parts_order = ref 0 in
  let next_order () =
    let k = !parts_order in
    incr parts_order;
    (n, k)
  in
  let op_full cl = match Tree.get_resolved cl with Some (Tree.ROp op) -> Some (op, false) | Some (Tree.RNeverOp op) -> Some (op, true) | _ -> None in
  let ops = List.filter_map (fun cl -> Option.map (fun o -> (cl, o)) (op_full cl)) clauses in
  let effect =
    match ops with
    | (_, (op, _)) :: _ -> effect_sym env.tb (Type.intern (fst (split_last_dot (Type.name_of op))))
    | [] -> bug "KIR の書き出し: 操作節の無い handle です"
  in
  let arg_pats (c : T.clause') = match snd c.T.cl_pat with T.PCtor (_, aps) -> List.map (fun (ap : T.ctor_arg_pat) -> ap.T.cap_pat) aps | _ -> [] in
  (* 本体 *)
  let body_part =
    let sym = base ^ ".body" in
    let fr = new_frame ~parent:env.fr ~root:r ~sym ~kind:I.Handlebody ~params:[] ~owner:env.fr.fr_owner () in
    let b = exp { env with fr; tail = false; spine = false } body in
    finish fr ~order:(next_order ()) { pd_yield = true; pd_dicts = 0; pd_result = rep_of_node body; pd_pats = []; pd_guard = None; pd_body = b };
    { I.p_fn = sym; p_caps = [] }
  in
  (* 操作節 *)
  let seen = Hashtbl.create 4 in
  let op_parts =
    List.map
      (fun (((_, c) : T.clause), (op, never)) ->
        let o = snd (split_last_dot (Type.name_of op)) in
        let k = Option.value ~default:0 (Hashtbl.find_opt seen o) in
        Hashtbl.replace seen o (k + 1);
        let sym = base ^ ".op." ^ o ^ if k = 0 then "" else "#" ^ string_of_int k in
        let ps = arg_pats c in
        let fr = new_frame ~parent:env.fr ~root:r ~sym ~kind:I.Opclause ~params:(List.map rep_of_node ps) ~owner:None () in
        if not never then fr.fr_owner <- Some fr;
        let env0 = { env with fr; tail = false; spine = false } in
        let env1, pats =
          List.fold_left
            (fun (env, acc) (j, p) ->
              let q = strip_annot p in
              match snd q with
              | T.PVar x -> (bind_name env x (I.VLocal j), I.PWild :: acc)
              | T.PWildcard -> (env, I.PWild :: acc)
              | _ ->
                  let ip, env' = local_pat env p in
                  (env', ip :: acc))
            (env0, [])
            (List.mapi (fun j p -> (j, p)) ps)
        in
        let pats = List.rev pats in
        let guard = Option.map (exp (nt env1)) c.T.cl_guard in
        let b = exp { env1 with tail = never && env.tail; spine = not never } c.T.cl_body in
        let cls = if never then I.N else if fr.fr_ntail_resumes = 0 then I.T else I.G in
        finish fr ~order:(next_order ()) { pd_yield = true; pd_dicts = 0; pd_result = rep_of_node c.T.cl_body; pd_pats = pats; pd_guard = guard; pd_body = b };
        (o, cls, { I.p_fn = sym; p_caps = [] }))
      ops
  in
  let find tag = List.find_opt (fun cl -> Tree.get_resolved cl = Some tag) clauses in
  let ret_part =
    match find Tree.RReturnClause with
    | None -> None
    | Some (_, c) ->
        let sym = base ^ ".return" in
        let ps = arg_pats c in
        let fr = new_frame ~parent:env.fr ~root:r ~sym ~kind:I.Retclause ~params:(List.map rep_of_node ps) ~owner:None () in
        let b = lambda_body { env with fr; tail = env.tail; spine = false } ps c.T.cl_body in
        finish fr ~order:(next_order ()) { pd_yield = true; pd_dicts = 0; pd_result = rep_of_node c.T.cl_body; pd_pats = []; pd_guard = None; pd_body = b };
        Some { I.p_fn = sym; p_caps = [] }
  in
  let cancel_part =
    match find Tree.RCancelClause with
    | None -> None
    | Some (_, c) ->
        let sym = base ^ ".cancel" in
        let fr = new_frame ~parent:env.fr ~root:r ~sym ~kind:I.Cancelclause ~params:[] ~owner:None () in
        let b = exp { env with fr; tail = false; spine = false } c.T.cl_body in
        finish fr ~order:(next_order ()) { pd_yield = true; pd_dicts = 0; pd_result = rep_of_node c.T.cl_body; pd_pats = []; pd_guard = None; pd_body = b };
        Some { I.p_fn = sym; p_caps = [] }
  in
  I.Handle { I.h_tail = env.tail; h_effect = effect; h_body = body_part; h_ops = op_parts; h_return = ret_part; h_cancel = cancel_part }

(* ## 18.11 キャプチャの番号の確定

   ルート関数を書き終えたら、書き出した関数を作った順(親が先)にたどり、キャプチャの並びを決める。
   親の関数の番号はすでに確定しているので、
   キャプチャの並びを親の関数での読み方に直してから並べられる。
   並べる順は、辞書の引数、キャプチャ、スロットの順で、
   それぞれの中では番号の昇順である(IRSpec 6.5 節)。

   その後で、各関数の本体の仮の番号を確定した番号に置き換え、
   生成箇所の式にキャプチャの並びを書き込む。
   生成箇所の式が作る関数は、その関数のシンボルで引く。 *)
let var_key = function I.VDParam i -> (0, i) | I.VEnv i -> (1, i) | I.VLocal i -> (2, i)

let slot_rep fr i =
  let all = fr.fr_params @ List.rev fr.fr_locals in
  match List.nth_opt all i with Some r -> r | None -> bug "KIR の書き出し: スロットの番号が範囲の外です"

let fix_caps fr =
  match fr.fr_parent with
  | None -> if fr.fr_caps <> [] then bug "KIR の書き出し: 根の関数が捕獲を持っています"
  | Some p ->
      let resolve = function I.VEnv t -> I.VEnv (List.assoc t p.fr_subst) | v -> v in
      let resolved = List.map (fun (id, v) -> (id, resolve v)) fr.fr_caps in
      let sorted = List.stable_sort (fun (_, a) (_, b) -> compare (var_key a) (var_key b)) resolved in
      fr.fr_subst <- List.mapi (fun i (id, _) -> (id, i)) sorted;
      fr.fr_final_caps <- List.map snd sorted;
      fr.fr_cap_reps <-
        List.map (function I.VLocal i -> slot_rep p i | I.VDParam _ -> I.RAny | I.VEnv j -> List.nth p.fr_cap_reps j) fr.fr_final_caps

let rewrite (sites : (string, frame) Hashtbl.t) fr body =
  let sub t = match List.assoc_opt t fr.fr_subst with Some i -> i | None -> bug "KIR の書き出し: 捕獲の仮の番号がありません" in
  let var = function I.VEnv t -> I.VEnv (sub t) | v -> v in
  let caps_of sym = match Hashtbl.find_opt sites sym with Some f -> f.fr_final_caps | None -> bug ("KIR の書き出し: 場所の関数がありません: " ^ sym) in
  let part p = { p with I.p_caps = caps_of p.I.p_fn } in
  let rec d = function
    | I.DInst (i, ps) -> I.DInst (i, List.map d ps)
    | I.DVar v -> I.DVar (var v)
    | I.DRecord fs -> I.DRecord (List.map (fun (l, x) -> (l, d x)) fs)
    | I.DVariant fs -> I.DVariant (List.map (fun (l, x) -> (l, d x)) fs)
    | I.DBuiltin _ as x -> x
  in
  let rec e = function
    | (I.Lit _ | I.Lit_error _ | I.Local _ | I.Global _ | I.Rec_empty | I.Hole) as x -> x
    | I.Env t -> I.Env (sub t)
    | I.Construct (t, c, fs) -> I.Construct (t, c, List.map (fun (i, x) -> (i, e x)) fs)
    | I.Variant (l, x) -> I.Variant (l, e x)
    | I.Call c -> I.Call { c with I.c_fn = e c.I.c_fn; c_args = List.map e c.I.c_args }
    | I.Method (c, m, x, os) -> I.Method (c, m, d x, List.map d os)
    | I.Opcall (c, m, x, args) -> I.Opcall (c, m, d x, List.map e args)
    | I.Not x -> I.Not (e x)
    | I.And (a, b) -> I.And (e a, e b)
    | I.Or (a, b) -> I.Or (e a, e b)
    | I.Closure (f, _) -> I.Closure (f, caps_of f)
    | I.Dictabs (f, _) -> I.Dictabs (f, caps_of f)
    | I.Dictapp (x, ds) -> I.Dictapp (e x, List.map d ds)
    | I.Let (i, a, b) -> I.Let (i, e a, e b)
    | I.Letpat (p, a, b) -> I.Letpat (p, e a, e b)
    | I.Letrec (items, b) -> I.Letrec (List.map (fun (i, x) -> (i, e x)) items, e b)
    | I.Seq xs -> I.Seq (List.map e xs)
    | I.Match (x, cls) -> I.Match (e x, List.map (fun c -> { c with I.cl_guard = Option.map e c.I.cl_guard; cl_body = e c.I.cl_body }) cls)
    | I.Rec_extend (l, v, r) -> I.Rec_extend (l, e v, e r)
    | I.Rec_select (l, x) -> I.Rec_select (l, e x)
    | I.Rec_restrict (l, x) -> I.Rec_restrict (l, e x)
    | I.Rec_update (l, r, v) -> I.Rec_update (l, e r, e v)
    | I.Perform (f, o, args) -> I.Perform (f, o, List.map e args)
    | I.Handle h ->
        I.Handle
          {
            h with
            I.h_body = part h.I.h_body;
            h_ops = List.map (fun (o, c, p) -> (o, c, part p)) h.I.h_ops;
            h_return = Option.map part h.I.h_return;
            h_cancel = Option.map part h.I.h_cancel;
          }
    | I.Resume (t, x) -> I.Resume (t, e x)
  in
  e body

(* ルート関数を 1 つ書き出す。返り値は、ルート関数に続けて、
   持ち上げた関数を生成箇所の番号の順に並べたリストである。
   ハンドラ式の生成箇所が作る関数は、本体、操作節、return 節、cancel 節の順に並ぶ *)
let root_fn tb ~sym ~kind ~params ~dicts ~dkeys ~tail ~yield ~result mk_body =
  let r = { r_sym = sym; r_sites = 0; r_frames = []; r_fns = [] } in
  let fr = new_frame ~root:r ~sym ~kind ~params ~owner:None () in
  let env = bind_dkeys { tb; fr; names = SMap.empty; dkeys = DK.empty; tail; spine = false } dkeys 0 in
  let body = mk_body env in
  let frames = List.rev r.r_frames in
  List.iter fix_caps frames;
  let sites = Hashtbl.create 16 in
  List.iter (fun f -> Hashtbl.replace sites f.fr_sym f) frames;
  let mk f pd =
    {
      I.f_sym = f.fr_sym;
      f_kind = f.fr_kind;
      f_yield = pd.pd_yield;
      f_params = f.fr_params;
      f_locals = List.rev f.fr_locals;
      f_dicts = pd.pd_dicts;
      f_caps = f.fr_cap_reps;
      f_result = pd.pd_result;
      f_pats = pd.pd_pats;
      f_guard = Option.map (rewrite sites f) pd.pd_guard;
      f_body = rewrite sites f pd.pd_body;
    }
  in
  let root = mk fr { pd_yield = yield; pd_dicts = dicts; pd_result = result; pd_pats = []; pd_guard = None; pd_body = body } in
  let lifted = List.stable_sort (fun (a, _, _) (b, _, _) -> compare a b) (List.rev r.r_fns) in
  root :: List.map (fun (_, f, pd) -> mk f pd) lifted

(* 種類が lambda のルート関数(関数の定義と let rec の項目)を書き出す *)
let root_lambda tb ~sym ~params ~body ~fn_node =
  root_fn tb ~sym ~kind:I.Lambda ~params:(List.map rep_of_node params) ~dicts:0 ~dkeys:[] ~tail:true ~yield:(yield_of_node tb fn_node)
    ~result:(rep_of_node body) (fun env -> lambda_body env params body)

(* 種類が thunk のルート関数(初期化式と式文)を書き出す *)
let root_thunk tb ~sym ~result mk_body = root_fn tb ~sym ~kind:I.Thunk ~params:[] ~dicts:0 ~dkeys:[] ~tail:false ~yield:true ~result mk_body

(* 種類が dictabs のルート関数を書き出す *)
let root_dictabs tb ~sym ~dkeys ~result mk_body =
  root_fn tb ~sym ~kind:I.Dictabs_fn ~params:[] ~dicts:(List.length dkeys) ~dkeys ~tail:false ~yield:true ~result mk_body

(* ## 18.12 宣言の変換規則

   各単位のトップレベルの宣言を、書いた順に初期化手順とグローバルに変換する(IRSpec 10.2 節)。

   | 宣言 | 初期化手順 | グローバルの種類 |
   |---|---|---|
   | 関数の定義の `let` | `def_fns` | 辞書を受け取らなければ `fn`、受け取れば `dictabs` |
   | 値の `let`(名前が変数) | 辞書を受け取らなければ `def_value`、受け取れば `def_dictabs` | `value` か `dictabs` |
   | 値の `let`(名前が変数以外のパターン) | `def_pattern` | 束縛する変数ごとに `value` |
   | `let rec` | グループ全体で 1 つの `def_fns` | 項目ごとに `fn` か `dictabs` |
   | `extern` | `def_fns` | `extern` |
   | `type instance` | `def_instance` | なし |
   | 式文 | 辞書を受け取らなければ `run_exp`、受け取れば何も書かない | なし |

   `def_pattern` と `run_exp` の関数のシンボルは `単位の鍵/$init<k>` である。
   `k` は、その初期化手順が単位の初期化手順の並びの中で何番目かを表す、0 始まりの番号である。
   何も書かない式文は初期化手順を作らないので、番号を使わない。

   辞書を受け取る値束縛の名前が変数以外のパターンのとき、
   第14章は辞書を受け取る値をそのパターンと照合するので、照合に失敗する。
   `_` だけは照合に成功し、何も束縛しない。
   本章も、初期化式を `dictabs` の生成箇所にして得た値をパターンと照合する KIR を書き、
   同じ結果にする。

   インスタンスの対象の型は、第14章の `exec_decl` と同じ方法で求める。
   宣言が属する module と単位を現在の module と単位に設定してから、
   クラスと型構成子の名前を解決する。 *)
let instance_head node (i : T.instance_decl') =
  Decls.with_decl_scope (Tree.oid_of node) @@ fun () ->
  let cls = Decls.resolve_class (Type.intern i.T.ins_class) in
  let con =
    match i.T.ins_args with
    | [ (_, T.EIdent (LongId comps)) ] | [ (_, T.EApply ((_, T.EIdent (LongId comps)), _)) ] ->
        Decls.resolve_con (Type.intern (String.concat "." comps))
    | _ -> bug "KIR の書き出し: インスタンスの頭を解決できません"
  in
  (cls, con)

(* 単位の型、エフェクト、クラスの表を作る(第 1 段階の前半)。
   第 1 段階の後半は、インスタンスのクラスと対象の型、
   `def_pattern` のパターンに現れるコンストラクタの型を、この表でシンボルに直す。
   そのため、すべての単位の表を先に作っておく *)
let collect_types tb (u : unit_src) =
  let key = u.us_key in
  let sym name = key ^ "/" ^ Type.display name in
  List.concat_map
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DNewtype n ->
          let s = sym n.T.nt_name in
          Hashtbl.replace tb.types (Type.intern n.T.nt_name) s;
          let (T.NtCtors cs) = n.T.nt_rhs in
          [ `Type { I.t_sym = s; t_ctors = List.map (fun (c : T.ctor_decl) -> { I.ct_name = Type.display c.T.cd_name; ct_arity = List.length c.T.cd_fields }) cs } ]
      | T.DEffect e ->
          let s = sym e.T.ef_name in
          let eoid = Type.intern e.T.ef_name in
          Hashtbl.replace tb.effects eoid s;
          let info = match Decls.find_effect eoid with Some i -> i | None -> bug ("KIR の書き出し: エフェクトがありません: " ^ e.T.ef_name) in
          let ops =
            List.map
              (fun (o, _) ->
                let scheme = match List.assoc_opt (Type.intern o) info.Decls.ef_ops with Some s -> s | None -> bug ("KIR の書き出し: 操作がありません: " ^ o) in
                let arity, never =
                  match Type.repr scheme with
                  | Type.TArrow (a, r, _) ->
                      let n = match Type.repr a with Type.TRecord row -> List.length (fst (Type.row_fields row)) | _ -> 0 in
                      (n, match Type.repr r with Type.TCon (c, []) -> c = Type.intern "Never" | _ -> false)
                  | _ -> bug "KIR の書き出し: 操作の型が関数の型ではありません"
                in
                { I.o_name = o; o_arity = arity; o_never = never; o_runtime = s = "prelude/Console" && o = "write" && arity = 1 })
              e.T.ef_ops
          in
          [ `Effect { I.e_sym = s; e_ops = ops } ]
      | T.DClass c ->
          let s = sym c.T.cls_name in
          let coid = Type.intern c.T.cls_name in
          Hashtbl.replace tb.classes coid s;
          let ci = match Decls.find_class coid with Some ci -> ci | None -> bug ("KIR の書き出し: クラスがありません: " ^ c.T.cls_name) in
          let methods =
            List.map
              (fun (v : T.class_val) ->
                let scheme = match List.assoc_opt v.T.cv_name ci.Decls.ci_methods with Some s -> s | None -> bug "KIR の書き出し: メソッドがありません" in
                (v.T.cv_name, List.length (Unify.constraints_of scheme) - 1))
              c.T.cls_vals
          in
          [ `Class { I.c_sym = s; c_methods = methods } ]
      | _ -> [])
    u.us_decls

(* 単位のグローバル、インスタンス、初期化手順を決める(第 1 段階の後半)。
   ルート関数は第 2 段階で書くので、ルート関数を書き出す処理をクロージャにして、
   初期化手順の順に返す *)
let collect_unit tb (u : unit_src) =
  let key = u.us_key in
  let counts = Hashtbl.create 32 in
  let numbered tbl q =
    let n = Option.value ~default:0 (Hashtbl.find_opt tbl q) in
    Hashtbl.replace tbl q (n + 1);
    if n = 0 then q else q ^ "#" ^ string_of_int n
  in
  let globals = ref [] in
  let steps = ref [] in
  let roots = ref [] in
  let instances = ref [] in
  let inst_counts = Hashtbl.create 8 in
  let new_global oid x kind_of =
    let g = key ^ "/" ^ numbered counts (Type.display x) in
    Hashtbl.replace tb.globals (oid, x) g;
    globals := { I.g_sym = g; g_kind = kind_of g } :: !globals;
    g
  in
  let step s = steps := s :: !steps in
  let root f = roots := f :: !roots in
  let init_sym () = key ^ "/$init" ^ string_of_int (List.length !steps) in
  let fn_def_root g bnode ~params ~body ~fn_node =
    match dict_params_of bnode with
    | [] -> root (fun () -> root_lambda tb ~sym:g ~params ~body ~fn_node)
    | ks -> root (fun () -> root_dictabs tb ~sym:g ~dkeys:ks ~result:I.RAny (fun env -> lambda_site env ~params ~body ~fn_node))
  in
  List.iter
    (fun (((_, d) as node) : T.decl) ->
      match d with
      | T.DLet (((_, b) as bnode) : T.let_binding) -> (
          let name = strip_annot b.T.lb_name in
          let ks = dict_params_of bnode in
          match (b.T.lb_params, snd name) with
          | Some ps, T.PVar x ->
              let g = new_global (Tree.oid_of bnode) x (fun g -> if ks = [] then I.GFn g else I.GDictabs g) in
              step (I.Def_fns [ g ]);
              fn_def_root g bnode ~params:ps ~body:b.T.lb_body ~fn_node:(fst bnode, ())
          | Some _, _ -> bug "KIR の書き出し: 関数の定義の名前が変数ではありません"
          | None, T.PVar x when ks <> [] ->
              let g = new_global (Tree.oid_of bnode) x (fun g -> I.GDictabs g) in
              step (I.Def_dictabs g);
              root (fun () -> root_dictabs tb ~sym:g ~dkeys:ks ~result:(rep_of_node b.T.lb_body) (fun env -> exp env b.T.lb_body))
          | None, T.PVar x ->
              let g = new_global (Tree.oid_of bnode) x (fun _ -> I.GValue (rep_of_name name bnode)) in
              step (I.Def_value (g, g));
              root (fun () -> root_thunk tb ~sym:g ~result:(rep_of_node b.T.lb_body) (fun env -> exp env b.T.lb_body))
          | None, _ ->
              let f = init_sym () in
              let gs = ref [] in
              let p =
                pat tb b.T.lb_name ~bind:(fun x pnode ->
                    let g = new_global (Tree.oid_of bnode) x (fun _ -> I.GValue (rep_of_node pnode)) in
                    gs := g :: !gs;
                    List.length !gs - 1)
              in
              step (I.Def_pattern (f, List.rev !gs, p));
              let result = rep_of_node b.T.lb_body in
              root (fun () ->
                  root_thunk tb ~sym:f ~result:(if ks = [] then result else I.RAny) (fun env ->
                      match ks with [] -> exp env b.T.lb_body | ks -> dictabs_site env ks ~result (fun env -> exp env b.T.lb_body))))
      | T.DLetRec bs ->
          let gs =
            List.map
              (fun (((_, b) as bnode) : T.let_binding) ->
                match snd (strip_annot b.T.lb_name) with
                | T.PVar x -> new_global (Tree.oid_of bnode) x (fun g -> if dict_params_of bnode = [] then I.GFn g else I.GDictabs g)
                | _ -> bug "KIR の書き出し: let rec の名前が変数ではありません")
              bs
          in
          step (I.Def_fns gs);
          List.iter2
            (fun g (((_, b) as bnode) : T.let_binding) ->
              match b.T.lb_params with
              | Some ps -> fn_def_root g bnode ~params:ps ~body:b.T.lb_body ~fn_node:(fst bnode, ())
              | None -> (
                  match snd b.T.lb_body with
                  | T.Lambda { l_params; l_body } -> fn_def_root g bnode ~params:l_params ~body:l_body ~fn_node:(fst b.T.lb_body, ())
                  | _ -> bug "KIR の書き出し: let rec の右辺が関数ではありません"))
            gs bs
      | T.DExtern ex ->
          let dicts = match Tree.get_dict node with Tree.DAbs ks -> List.length ks | _ -> 0 in
          let abi = if ex.T.ex_abi = "C" then I.C else I.Prim in
          let g = new_global (Tree.oid_of node) ex.T.ex_name (fun _ -> I.GExtern { abi; impl = ex.T.ex_prim; dicts }) in
          step (I.Def_fns [ g ])
      | T.DExp e -> (
          match Tree.get_dict node with
          | Tree.DAbs _ -> ()
          | _ ->
              let f = init_sym () in
              step (I.Run_exp f);
              root (fun () -> root_thunk tb ~sym:f ~result:(rep_of_node e) (fun env -> exp env e)))
      | T.DInstance i ->
          let cls, con = instance_head node i in
          let csym = class_sym tb cls and hsym = type_sym tb con in
          let isym = key ^ "/" ^ numbered inst_counts ("instance:" ^ sym_name csym ^ "[" ^ sym_name hsym ^ "]") in
          Hashtbl.replace tb.instances (cls, con) isym;
          let pk = match Tree.get_dict node with Tree.DInstance ks -> ks | _ -> [] in
          let np = List.length pk in
          let method_info bnode = match Tree.get_dict bnode with Tree.DMethod (_, mk, ad) -> (mk, ad) | _ -> ([], []) in
          let methods = ref [] in
          let method_root x bnode mk_v =
            let mk, adapter = method_info bnode in
            let fsym = isym ^ "." ^ x in
            methods := (x, List.length mk, fsym) :: !methods;
            root (fun () ->
                root_dictabs tb ~sym:fsym ~dkeys:(pk @ mk) ~result:I.RAny (fun env ->
                    let v = mk_v env in
                    match adapter with [] -> v | hs -> I.Dictapp (v, List.map (fun h -> dict env (Tree.EvHole h)) hs)))
          in
          List.iter
            (fun ((_, d) : T.decl) ->
              match d with
              | T.DLet (((_, b) as bnode) : T.let_binding) -> (
                  match snd (strip_annot b.T.lb_name) with
                  | T.PVar x -> method_root x bnode (fun env -> binding_value env bnode)
                  | _ -> ())
              | T.DLetRec bs ->
                  List.iter
                    (fun (((_, b) as bnode) : T.let_binding) ->
                      match snd (strip_annot b.T.lb_name) with
                      | T.PVar x ->
                          method_root x bnode (fun env ->
                              let env', items = rec_group env bs in
                              let slot = match SMap.find_opt x env'.names with Some { b_var = I.VLocal n; _ } -> n | _ -> bug "KIR の書き出し: let rec の名前" in
                              I.Letrec (items, I.Local slot))
                      | _ -> ())
                    bs
              | _ -> ())
            i.T.ins_body;
          instances := { I.i_sym = isym; i_class = csym; i_head = hsym; i_premises = np; i_methods = List.rev !methods } :: !instances;
          step (I.Def_instance isym)
      | T.DType _ | T.DNewtype _ | T.DEffect _ | T.DClass _ -> ()
      | T.DModule _ -> bug "KIR の書き出し: module が平坦化されていません")
    u.us_decls;
  (List.rev !globals, List.rev !steps, List.rev !roots, List.rev !instances)

(* ## 18.13 プログラム

   単位は、組み込み、プレリュード、import した単位、起点の順に並べる。
   型、クラス、グローバルの表は、組み込みの項目(IRSpec 付録 A の順)を先頭に置き、単位の順に続ける。
   関数表は、単位の順、初期化手順の順にルート関数を並べ、
   各ルート関数の後に、そのルート関数から持ち上げた関数を置く。 *)
let program (units : unit_src list) : I.program =
  provisional := 0;
  let tb = new_tables () in
  List.iter (fun t -> Hashtbl.replace tb.types (Type.intern t) ("builtin/" ^ t)) builtin_types;
  List.iter (fun (c, _) -> Hashtbl.replace tb.classes (Type.intern c) ("builtin/" ^ c)) builtin_classes;
  let decls_tables = List.map (collect_types tb) units in
  let collected = List.map (collect_unit tb) units in
  let pick f = List.concat_map (List.filter_map f) decls_tables in
  let types = pick (function `Type t -> Some t | _ -> None) in
  let effects = pick (function `Effect e -> Some e | _ -> None) in
  let classes = pick (function `Class c -> Some c | _ -> None) in
  let functions = List.concat_map (fun (_, _, roots, _) -> List.concat_map (fun f -> f ()) roots) collected in
  {
    I.version = I.version;
    units =
      { I.u_key = "builtin"; u_paths = []; u_init = [] }
      :: List.map2 (fun u (_, steps, _, _) -> { I.u_key = u.us_key; u_paths = u.us_paths; u_init = steps }) units collected;
    types = List.map (fun t -> { I.t_sym = "builtin/" ^ t; t_ctors = [] }) builtin_types @ types;
    effects;
    classes = List.map (fun (c, ms) -> { I.c_sym = "builtin/" ^ c; c_methods = List.map (fun m -> (m, 0)) ms }) builtin_classes @ classes;
    instances = List.concat_map (fun (_, _, _, is) -> is) collected;
    globals = List.map (fun v -> { I.g_sym = "builtin/" ^ v; g_kind = I.GBuiltin }) builtin_values @ List.concat_map (fun (gs, _, _, _) -> gs) collected;
    functions;
  }
