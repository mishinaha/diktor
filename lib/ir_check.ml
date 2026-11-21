(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第21章 KIR の検証

   本章は、読み込んだ `Ir.program` が KIR の規則を満たすことを検証する。
   仕様は親リポジトリの `doc/IRSpec.md` の 13.8 節(検証)と 13.9 節(入れ子の上限)が定める。
   第20章の読み込みはバイトの並びと添字の範囲を検査し、本章はそれを前提にして、
   残りの規則を検査する。
   検証に通ったプログラムでは、評価器がシンボルを表で解決できずに失敗することも、
   末尾の印や操作節の分類を信じて誤った動作をすることもない。

   検証は型の健全性を保証しない。
   型の健全性は、型検査を済ませたライタが保証する。
   本章が検査するのは、型を使わずに計算できる性質だけである。

   | 性質 | 検査する内容 |
   |---|---|
   | 名前 | 表ごとにシンボルが一意で、`単位の鍵/名前` の形式であり、参照するシンボルが表にある |
   | 組み込みの表 | 組み込みの型、クラス、値が付録 A の順で表の先頭にあり、ほかに組み込みの項目がない |
   | 操作の印 | `runtime` の印はプレリュードの `Console` の `write` だけに付き、プログラムはそのエフェクトを `handle` しない |
   | 関数のフィールド | 引数、辞書の引数、キャプチャの個数が関数の種類に合い、種類が関数の生成箇所に合う |
   | スロット | 番号がテキストの順に 1 ずつ増え、範囲内にあり、束縛のスコープの中でだけ読む |
   | キャプチャ | 個数と Rep が、作られる関数のフィールドと合う |
   | 辞書 | 使う位置のクラスと辞書のクラスが合い、`dictapp` の辞書の個数が受け取る側と合う |
   | インスタンス | クラスの各メソッドの実装をちょうど 1 個ずつ持つ |
   | 末尾の印 | 再計算した末尾位置と一致する |
   | 操作節の分類 | 再計算した N、T、G と一致する |
   | `resume` の位置 | 操作節の本体か、その中のハンドラ式の本体の中だけにある |
   | 初期化 | グローバルとインスタンスをちょうど 1 回ずつ定義する |

   表の中の `単位の鍵/名前` は診断メッセージの表記で、「単位の鍵」は単位のキーを指す。
   検証は、最初に見つけたエラーのメッセージを返し、残りは調べない。 *)
open Ir

exception Invalid of string

let fail fmt = Printf.ksprintf (fun s -> raise (Invalid s)) fmt

(* ## 21.1 表

   表ごとに、シンボルから項目を引くハッシュ表を作る。
   同じシンボルが 2 回現れる表は、シンボルで項目を指定できないので拒否する。
   コンストラクタ、操作、メソッドの名前も、それを持つ型、エフェクト、
   クラスの中で一意でなければならない。
   テキストはこれらを名前で書くので、同じ名前が 2 つあると、名前から項目を決められないからである。

   シンボルは `単位の鍵/名前` の形式でなければならない。
   最後の `/` の後ろの名前は空でなく、前の部分は単位の表にあるキーである。
   単位のキーはシンボルから決まる。
   §21.7 と §21.8 はそのキーを使って、グローバルやインスタンスが、
   それを定義する初期化手順を持つ単位のものかどうかと、組み込みの項目かどうかを判定する。
   `/` を含まないシンボルや、どの単位のキーでもない文字列を前の部分に持つシンボルを受理すると、
   その判定がリーダごとに分かれる。 *)
let table what key items =
  let h = Hashtbl.create (List.length items * 2 + 1) in
  List.iter
    (fun x ->
      let k = key x in
      if Hashtbl.mem h k then fail "%sの記号が重なります: %s" what k;
      Hashtbl.replace h k x)
    items;
  h

let unique what owner names =
  let h = Hashtbl.create 8 in
  List.iter
    (fun n ->
      if Hashtbl.mem h n then fail "%s %s の中で名前 %s が重なります" what owner n;
      Hashtbl.replace h n ())
    names

let symbol_form units what sym =
  match String.rindex_opt sym '/' with
  | None -> fail "%sの記号 %s が 単位の鍵/名前 の形ではありません" what sym
  | Some i ->
      if i = String.length sym - 1 then fail "%sの記号 %s の名前の部分が空です" what sym;
      if not (Hashtbl.mem units (String.sub sym 0 i)) then fail "%sの記号 %s の単位の鍵 %s が単位の表にありません" what sym (String.sub sym 0 i)

let get what h k = match Hashtbl.find_opt h k with Some x -> x | None -> fail "%sが表にありません: %s" what k

type env = {
  types : (string, ty) Hashtbl.t;
  effects : (string, eff) Hashtbl.t;
  classes : (string, cls) Hashtbl.t;
  instances : (string, instance) Hashtbl.t;
  globals : (string, global) Hashtbl.t;
  fns : (string, fn) Hashtbl.t;
  max_nest : int;
}

let ctor_of env t c =
  let ty = get "型" env.types t in
  match List.find_opt (fun x -> x.ct_name = c) ty.t_ctors with Some x -> x | None -> fail "型 %s にコンストラクタ %s がありません" t c

let op_of env e o =
  let ef = get "エフェクト" env.effects e in
  match List.find_opt (fun x -> x.o_name = o) ef.e_ops with Some x -> x | None -> fail "エフェクト %s に操作 %s がありません" e o

(* `runtime` の印が付く操作なら真を返す。
   規則は §21.8 で述べる。 *)
let is_runtime_op (e : eff) (o : op) = e.e_sym = "prelude/Console" && o.o_name = "write" && o.o_arity = 1

let method_of env c m =
  let cl = get "クラス" env.classes c in
  match List.assoc_opt m cl.c_methods with Some k -> k | None -> fail "クラス %s にメソッド %s がありません" c m

(* ## 21.2 関数の生成箇所

   関数表のどの関数にも、それを作る箇所(生成箇所)がちょうど 1 つある。
   ルート関数は、グローバル、初期化手順、インスタンスのどれか 1 つの項目が指す。
   持ち上げた関数(ラムダリフティングで取り出した関数)は、
   関数の本体かガードの中にある `closure`、`dictabs`、`handle` の部分(本体、操作節、`return` 節、
   `cancel` 節)のどれか 1 つが指す。
   生成箇所を含む関数は、通常は持ち上げた関数とは別の関数である。
   ただし検証は、関数が自身の本体かガードの中の生成箇所で作られることも拒否しない(§21.6)。
   関数の種類は、生成箇所ごとに決まっている。

   | 生成箇所 | 種類 |
   |---|---|
   | 種類が `fn` のグローバル、`closure` | `lambda` |
   | 種類が `dictabs` のグローバル、インスタンスのメソッドの実装、`dictabs` | `dictabs` |
   | `def_value`、`def_pattern`、`run_exp` | `thunk` |
   | `handle` の本体、操作節、`return` 節、`cancel` 節 | `handlebody`、`opclause`、`retclause`、`cancelclause` |

   `handle` の部分が指す関数については、末尾の印と操作節の分類を計算するときに、
   そのハンドラ式のフィールドを使う。
   そのため、持ち上げた関数ごとに、それを作った関数と、ハンドラ式のフィールドの値を記録する。
   記録するのは、ハンドラ式の末尾の印と、操作節ならエフェクト、操作、KIR に書いてある分類である。
   操作節のガードの中で作った関数かどうかも記録し、§21.6 で持ち主を決めるときに使う。 *)
type origin =
  | Root
  | Site of {
      parent : string;
      h_tail : bool;
      h_op : (string * string * clause_class) option; (* 操作節ならエフェクト、操作、KIR に書いてある分類 *)
      in_guard : bool; (* 操作節の guard のフィールドの中で作られたなら真 *)
    }

let kind_label = Ir.fn_kind_name

let rec sites_of_exp ?(in_guard = false) f acc e =
  let go = sites_of_exp ~in_guard f acc in
  match e with
  | Lit _ | Lit_error _ | Local _ | Env _ | Global _ | Rec_empty | Hole | Method _ -> ()
  | Closure (g, _) -> acc := (g, Lambda, Site { parent = f; h_tail = false; h_op = None; in_guard }) :: !acc
  | Dictabs (g, _) -> acc := (g, Dictabs_fn, Site { parent = f; h_tail = false; h_op = None; in_guard }) :: !acc
  | Construct (_, _, fs) -> List.iter (fun (_, e) -> go e) fs
  | Variant (_, e) | Not e | Rec_select (_, e) | Rec_restrict (_, e) | Resume (_, e) -> go e
  | Call c -> List.iter go (c.c_fn :: c.c_args)
  | Opcall (_, _, _, args) | Perform (_, _, args) -> List.iter go args
  | And (a, b) | Or (a, b) | Let (_, a, b) | Letpat (_, a, b) | Rec_extend (_, a, b) | Rec_update (_, a, b) ->
      go a;
      go b
  | Dictapp (e, _) -> go e
  | Letrec (items, e) ->
      List.iter (fun (_, e) -> go e) items;
      go e
  | Seq es -> List.iter go es
  | Match (e, cls) ->
      go e;
      List.iter
        (fun c ->
          Option.iter go c.cl_guard;
          go c.cl_body)
        cls
  | Handle h ->
      let site op = Site { parent = f; h_tail = h.h_tail; h_op = op; in_guard } in
      acc := (h.h_body.p_fn, Handlebody, site None) :: !acc;
      List.iter (fun (o, cls, p) -> acc := (p.p_fn, Opclause, site (Some (h.h_effect, o, cls))) :: !acc) h.h_ops;
      Option.iter (fun p -> acc := (p.p_fn, Retclause, site None) :: !acc) h.h_return;
      Option.iter (fun p -> acc := (p.p_fn, Cancelclause, site None) :: !acc) h.h_cancel

let origins (p : program) env =
  let h = Hashtbl.create 256 in
  let add (f, kind, o) =
    let fn = get "関数" env.fns f in
    if Hashtbl.mem h f then fail "関数 %s を作る場所が 2 つ以上あります" f;
    if fn.f_kind <> kind then fail "関数 %s の種類 %s が、作る場所の求める %s と違います" f (kind_label fn.f_kind) (kind_label kind);
    Hashtbl.replace h f o
  in
  List.iter
    (fun g -> match g.g_kind with GFn f -> add (f, Lambda, Root) | GDictabs f -> add (f, Dictabs_fn, Root) | GValue _ | GExtern _ | GBuiltin -> ())
    p.globals;
  List.iter
    (fun u ->
      List.iter
        (function
          | Def_value (_, f) | Def_pattern (f, _, _) | Run_exp f -> add (f, Thunk, Root)
          | Def_fns _ | Def_dictabs _ | Def_instance _ -> ())
        u.u_init)
    p.units;
  List.iter (fun i -> List.iter (fun (_, _, f) -> add (f, Dictabs_fn, Root)) i.i_methods) p.instances;
  List.iter
    (fun f ->
      let acc = ref [] in
      Option.iter (sites_of_exp ~in_guard:true f.f_sym acc) f.f_guard;
      sites_of_exp f.f_sym acc f.f_body;
      List.iter add (List.rev !acc))
    p.functions;
  List.iter (fun f -> if not (Hashtbl.mem h f.f_sym) then fail "関数 %s を作る場所がありません" f.f_sym) p.functions;
  h

(* ## 21.3 関数のフィールド

   関数の種類と生成箇所から、引数、辞書の引数、キャプチャの個数に次の制約が付く。

   - ルート関数はキャプチャを持たない。
   - 辞書の引数を持てるのは `dictabs` の関数だけである。
   - `lambda` の引数の個数は自由である。
     `dictabs`、`thunk`、`handlebody`、`cancelclause` は引数を持たず、
     `retclause` は引数を 1 個持つ。
   - 操作節の関数は、引数の個数が操作の引数の個数と同じで、引数ごとにパターンを 1 個持つ。
   - パターンとガードのフィールドを持てるのは操作節の関数だけである。 *)
let check_shape env origin f =
  let np = List.length f.f_params in
  let need what ok = if not ok then fail "関数 %s(%s)の%sが規則と合いません" f.f_sym (kind_label f.f_kind) what in
  (match origin with Root -> need "捕獲の数" (f.f_caps = []) | Site _ -> ());
  if f.f_kind <> Dictabs_fn then need "辞書の引数の数" (f.f_dicts = 0);
  if f.f_kind <> Opclause then need "パターンとガード" (f.f_pats = [] && f.f_guard = None);
  match f.f_kind with
  | Lambda -> ()
  | Dictabs_fn | Thunk | Handlebody | Cancelclause -> need "引数の数" (np = 0)
  | Retclause -> need "引数の数" (np = 1)
  | Opclause -> (
      need "パターンの数" (List.length f.f_pats = np);
      match origin with
      | Site { h_op = Some (e, o, _); _ } -> need "引数の数" (np = (op_of env e o).o_arity)
      | _ -> need "作る場所" false)

(* ## 21.4 本体

   本体は、関数ごとに次の状態を持ってたどる。

   - 次に束縛するスロットの番号。
     引数の個数から始まり、束縛する箇所をたどるたびに 1 増える。
   - スロットごとの、現在の位置が束縛のスコープの中にあるかどうか。
     引数は本体全体で有効である。
     `let N e1 e2` の `N` は `e2` の中だけで有効である。
     `letpat` のパターンが束縛するスロットは本体の式の中だけで、
     `match` の節のパターンが束縛するスロットは、その節のガードと本体の中だけで有効である。
     `letrec` のスロットは、項目のキャプチャと本体の式の中で有効である。
     `opclause` の `pats` が束縛するスロットは、ガードと本体の中で有効である。
     スコープの外で `local` を読む KIR は拒否する。
     スコープの外のスロットにリーダが何を置くかを仕様は定めていないので、
     読むとリーダごとに結果が分かれるからである。
   - その位置が末尾位置かどうか(`tail`)と、操作節の背骨の上にあるかどうか(`spine`)。
     背骨は、分類が N でない操作節(分類は §21.6)の本体から、末尾位置だけをたどった経路である。
   - ノードの深さ。
     入れ子の上限を超えたら拒否する。

   たどる順は正準なテキストの順で、操作節の関数では `pats`、`guard`、本体の順である。
   本体の中の `resume` は、末尾の印を検査したうえで、その印を関数ごとのリストに追加する。
   §21.6 は、このリストから操作節の分類を再計算する。 *)
type fstate = {
  fn : fn;
  slots : rep array;
  scope : bool array; (* スロットが束縛のスコープの中にあれば真 *)
  mutable next : int;
  mutable resumes : bool list;
  mutable in_guard : bool; (* 操作節の guard のフィールドをたどっている間は真 *)
}

let nest env d = if d > env.max_nest then fail "処理系の限度: KIR の検証で入れ子が深すぎます"

let var_ok st = function
  | VLocal i ->
      if i >= Array.length st.slots then fail "関数 %s: スロット %d が範囲外です" st.fn.f_sym i;
      if not st.scope.(i) then fail "関数 %s: スロット %d を束縛の有効範囲の外で読みます" st.fn.f_sym i
  | VEnv i -> if i >= List.length st.fn.f_caps then fail "関数 %s: 捕獲 %d が範囲外です" st.fn.f_sym i
  | VDParam i -> if i >= st.fn.f_dicts then fail "関数 %s: 辞書の引数 %d が範囲外です" st.fn.f_sym i

let var_rep st = function VLocal i -> st.slots.(i) | VEnv i -> List.nth st.fn.f_caps i | VDParam _ -> RAny

let bind st i =
  if i <> st.next then fail "関数 %s: スロット %d の束縛が現れる順と合いません(次は %d)" st.fn.f_sym i st.next;
  if i >= Array.length st.slots then fail "関数 %s: スロット %d が範囲外です" st.fn.f_sym i;
  st.next <- i + 1

(* 番号が `lo` から `hi - 1` までのスロットをスコープに入れて `k` を実行し、
   その後でスコープから外す。 *)
let scoped st lo hi k =
  for i = lo to hi - 1 do st.scope.(i) <- true done;
  k ();
  for i = lo to hi - 1 do st.scope.(i) <- false done

(* ラベルの並びが、ラベル名のバイト列の昇順であることを検査する。
   同じラベルが続くことは許す。 *)
let sorted_labels st what fs =
  let rec go = function a :: (b :: _ as rest) -> if compare a b > 0 then fail "関数 %s: %sのラベルが昇順に並んでいません" st.fn.f_sym what else go rest | _ -> () in
  go (List.map fst fs)

(* 組み込みのインスタンス(付録 A.3)を、(クラス, 型) の組の集合として持つ。
   評価器が引く第13章の実装の表 `builtin_method_table` から作る。
   この表のキーはクラス名、型構成子名、メソッド名の組で、そこからクラスと型の組を取り出す。
   そのため、評価器の表に実装がある組だけを受理する。 *)
let builtin_instances =
  let h = Hashtbl.create 32 in
  Hashtbl.iter (fun (c, t, _) _ -> Hashtbl.replace h ("builtin/" ^ c, "builtin/" ^ t) ()) Builtin.builtin_method_table;
  h

(* 辞書の式を検査する。
   `cls` は、その位置の辞書が属するべきクラスで、
   型を使わずにクラスがわかる位置でだけ `Some` である。
   クラスがわかるのは、`method` と `opcall` の `d` と、構造的な辞書の項目である。
   `d` のクラスはその `method` か `opcall` のクラスで、
   構造的な辞書の項目のクラスは `builtin/Eq` である。
   `dinst` の前提と `dictapp` の辞書は、
   インスタンス表と関数表が前提のクラスを持たないので `None` である。
   `dparam` と `env` の辞書のクラスは型で決まる性質なので、検査しない。 *)
let rec check_dict env st d ?cls dict =
  nest env d;
  let want what c =
    match cls with
    | Some k when k <> c -> fail "関数 %s: クラス %s の辞書の位置に、クラス %s の%sがあります" st.fn.f_sym k c what
    | _ -> ()
  in
  match dict with
  | DVar (VLocal _) -> fail "関数 %s: 辞書の式にスロットがあります" st.fn.f_sym
  | DVar v -> var_ok st v
  | DInst (i, ps) ->
      let inst = get "インスタンス" env.instances i in
      want "インスタンス" inst.i_class;
      if List.length ps <> inst.i_premises then fail "関数 %s: インスタンス %s の前提の数が違います" st.fn.f_sym i;
      List.iter (fun x -> check_dict env st (d + 1) x) ps
  | DRecord fs | DVariant fs ->
      want "構造的な辞書" "builtin/Eq";
      sorted_labels st "構造的な辞書" fs;
      List.iter (fun (_, x) -> check_dict env st (d + 1) ~cls:"builtin/Eq" x) fs
  | DBuiltin (c, t) ->
      ignore (get "クラス" env.classes c);
      ignore (get "型" env.types t);
      if not (Hashtbl.mem builtin_instances (c, t)) then fail "関数 %s: 組み込みのインスタンス %s[%s] は付録 A.3 にありません" st.fn.f_sym c t;
      want "組み込みのインスタンス" c

let rec check_pat env st d p =
  nest env d;
  match p with
  | PWild | PLit _ -> ()
  | PBind i -> bind st i
  | PRecord (fs, tl) -> (
      List.iter (fun (_, p) -> check_pat env st (d + 1) p) fs;
      match tl with Rest p -> check_pat env st (d + 1) p | Closed | Open -> ())
  | PCtor (t, c, fs) ->
      let ct = ctor_of env t c in
      let rec asc prev = function
        | (i, _) :: rest ->
            if i <= prev || i >= ct.ct_arity then fail "関数 %s: コンストラクタ %s のパターンのフィールドの位置 %d が不正です" st.fn.f_sym c i;
            asc i rest
        | [] -> ()
      in
      asc (-1) fs;
      List.iter (fun (_, p) -> check_pat env st (d + 1) p) fs
  | PVariant (_, p) -> check_pat env st (d + 1) p

(* 関数を作る部分(`closure`、`dictabs`、`handle` の各部分)のキャプチャの並びは、
   作られる関数の `caps` と個数が同じで、
   Rep も順に一致しなければならない。 *)
let check_part env st kind p =
  let g = get "関数" env.fns p.p_fn in
  if g.f_kind <> kind then fail "関数 %s: %s の種類が違います" st.fn.f_sym p.p_fn;
  if List.length p.p_caps <> List.length g.f_caps then fail "関数 %s: %s の捕獲の数が違います" st.fn.f_sym p.p_fn;
  List.iter2
    (fun v r ->
      var_ok st v;
      if var_rep st v <> r then fail "関数 %s: %s の捕獲の Rep が違います" st.fn.f_sym p.p_fn)
    p.p_caps g.f_caps

let mark st what want got = if want <> got then fail "関数 %s: %s の末尾の印が、再計算した結果と違います" st.fn.f_sym what

let rec check_exp env st d ~tail ~spine e =
  nest env d;
  let sub x = check_exp env st (d + 1) ~tail:false ~spine:false x in
  let cont x = check_exp env st (d + 1) ~tail ~spine x in
  let dict ?cls x = check_dict env st (d + 1) ?cls x in
  match e with
  | Lit _ | Lit_error _ | Rec_empty | Hole -> ()
  | Local i -> var_ok st (VLocal i)
  | Env i -> var_ok st (VEnv i)
  | Global g -> ignore (get "大域" env.globals g)
  | Construct (t, c, fs) ->
      let ct = ctor_of env t c in
      (* コンストラクタのフィールドの個数はファイルに書いてある任意の u32 なので、その長さの配列は作らない。
         ハッシュ表に入れる位置の個数は、式に書いてあるフィールドの個数以下である。 *)
      let seen = Hashtbl.create (List.length fs) in
      List.iter
        (fun (i, _) ->
          if i >= ct.ct_arity || Hashtbl.mem seen i then fail "関数 %s: コンストラクタ %s のフィールドの位置 %d が不正です" st.fn.f_sym c i;
          Hashtbl.replace seen i ())
        fs;
      if Hashtbl.length seen <> ct.ct_arity then fail "関数 %s: コンストラクタ %s のフィールドが足りません" st.fn.f_sym c;
      List.iter (fun (_, x) -> sub x) fs
  | Variant (_, x) | Not x | Rec_select (_, x) | Rec_restrict (_, x) -> sub x
  | Call c ->
      mark st "call" tail c.c_tail;
      List.iter sub (c.c_fn :: c.c_args)
  | Method (c, m, dd, os) ->
      let k = method_of env c m in
      if List.length os <> k then fail "関数 %s: メソッド %s の辞書の数が違います" st.fn.f_sym m;
      dict ~cls:c dd;
      List.iter (fun x -> dict x) os
  | Opcall (c, m, dd, args) ->
      if method_of env c m <> 0 then fail "関数 %s: 演算子の呼び出しのメソッド %s が自分の辞書を持ちます" st.fn.f_sym m;
      dict ~cls:c dd;
      List.iter sub args
  | And (a, b) | Or (a, b) ->
      sub a;
      cont b
  | Closure (f, cs) -> check_part env st Lambda { p_fn = f; p_caps = cs }
  | Dictabs (f, cs) -> check_part env st Dictabs_fn { p_fn = f; p_caps = cs }
  | Dictapp (x, ds) ->
      let n = List.length ds in
      let count what want = if n <> want then fail "関数 %s: %s に渡す辞書の数 %d が、受け取る数 %d と違います" st.fn.f_sym what n want in
      (match x with
       | Global g -> (
           match (get "大域" env.globals g).g_kind with
           | GExtern { dicts; _ } ->
               if dicts = 0 then fail "関数 %s: 辞書を受け取らない extern の大域 %s に辞書を渡します" st.fn.f_sym g;
               count g dicts
           | GDictabs f -> count g (get "関数" env.fns f).f_dicts
           | GFn _ | GValue _ | GBuiltin -> fail "関数 %s: 辞書を受け取らない大域 %s に辞書を渡します" st.fn.f_sym g)
       | Dictabs (f, _) -> count f (get "関数" env.fns f).f_dicts
       | _ -> ());
      sub x;
      List.iter (fun x -> dict x) ds
  | Let (i, a, b) ->
      bind st i;
      (match a with Closure _ | Dictabs _ -> if st.slots.(i) <> RAny then fail "関数 %s: 関数を束縛するスロット %d の Rep が any でありません" st.fn.f_sym i | _ -> ());
      sub a;
      scoped st i (i + 1) (fun () -> cont b)
  | Letpat (p, a, b) ->
      let lo = st.next in
      check_pat env st (d + 1) p;
      let hi = st.next in
      sub a;
      scoped st lo hi (fun () -> cont b)
  | Letrec (items, x) ->
      if items = [] then fail "関数 %s: letrec の項目がありません" st.fn.f_sym;
      let lo = st.next in
      List.iter
        (fun (i, _) ->
          bind st i;
          if st.slots.(i) <> RAny then fail "関数 %s: 関数を束縛するスロット %d の Rep が any でありません" st.fn.f_sym i)
        items;
      scoped st lo st.next (fun () ->
          List.iter (fun (_, x) -> match x with Closure _ | Dictabs _ -> sub x | _ -> fail "関数 %s: letrec の項目が closure でも dictabs でもありません" st.fn.f_sym) items;
          cont x)
  | Seq xs ->
      if List.length xs < 2 then fail "関数 %s: seq の要素が 2 個より少なくなっています" st.fn.f_sym;
      let rec go = function [ x ] -> cont x | x :: rest -> sub x; go rest | [] -> () in
      go xs
  | Match (x, cls) ->
      sub x;
      List.iter
        (fun c ->
          let lo = st.next in
          check_pat env st (d + 1) c.cl_pat;
          scoped st lo st.next (fun () ->
              Option.iter sub c.cl_guard;
              cont c.cl_body))
        cls
  | Rec_extend (_, a, b) | Rec_update (_, a, b) ->
      sub a;
      sub b
  | Perform (e, o, args) ->
      let op = op_of env e o in
      if List.length args <> op.o_arity then fail "関数 %s: 操作 %s の引数の数が違います" st.fn.f_sym o;
      List.iter sub args
  | Handle h ->
      mark st "handle" tail h.h_tail;
      if h.h_ops = [] then fail "関数 %s: ハンドラ式の操作節がありません" st.fn.f_sym;
      let ef = get "エフェクト" env.effects h.h_effect in
      if List.exists (is_runtime_op ef) ef.e_ops then fail "関数 %s: runtime の印の付いた操作を持つエフェクト %s を handle します" st.fn.f_sym h.h_effect;
      check_part env st Handlebody h.h_body;
      List.iter
        (fun (o, _, p) ->
          ignore (op_of env h.h_effect o);
          check_part env st Opclause p)
        h.h_ops;
      Option.iter (check_part env st Retclause) h.h_return;
      Option.iter (check_part env st Cancelclause) h.h_cancel
  | Resume (t, x) ->
      if st.in_guard then fail "関数 %s: 操作節のガードに resume があります" st.fn.f_sym;
      if t <> spine then fail "関数 %s: resume の末尾の印が、再計算した背骨と違います" st.fn.f_sym;
      st.resumes <- t :: st.resumes;
      sub x

(* ## 21.5 本体の最も外側の式の末尾位置

   関数の本体の最も外側の式が末尾位置かどうかは、関数の種類で決まる。
   `lambda` では末尾位置である。
   N の操作節と `return` 節では、その関数を作ったハンドラ式の印が `tail` のときだけ末尾位置である。
   それ以外の種類では末尾位置でない。
   N でない操作節では、本体の最も外側の式が背骨の上にあり、背骨はここから始まる。

   N かどうかは、KIR に書いてある分類ではなく、操作の `never` の印で決める。
   KIR に書いてある分類は、本体の `resume` から再計算して検査する対象だからである。 *)
let roots env origin f =
  let never = match origin with Site { h_op = Some (e, o, _); _ } -> (op_of env e o).o_never | _ -> false in
  let htail = match origin with Site { h_tail; _ } -> h_tail | Root -> false in
  let tail = match f.f_kind with Lambda -> true | Opclause -> never && htail | Retclause -> htail | _ -> false in
  (tail, f.f_kind = Opclause && not never)

let check_fn env origins f =
  let origin = Hashtbl.find origins f.f_sym in
  check_shape env origin f;
  let slots = Array.of_list (f.f_params @ f.f_locals) in
  let np = List.length f.f_params in
  let st = { fn = f; slots; scope = Array.init (Array.length slots) (fun i -> i < np); next = np; resumes = []; in_guard = false } in
  List.iter (check_pat env st 1) f.f_pats;
  for i = np to st.next - 1 do st.scope.(i) <- true done;
  Option.iter
    (fun g ->
      st.in_guard <- true;
      check_exp env st 1 ~tail:false ~spine:false g;
      st.in_guard <- false)
    f.f_guard;
  let tail, spine = roots env origin f in
  check_exp env st 1 ~tail ~spine f.f_body;
  if st.next <> Array.length st.slots then fail "関数 %s: 束縛されないスロットがあります(束縛は %d 個、スロットは %d 個)" f.f_sym st.next (Array.length st.slots);
  st.resumes

(* ## 21.6 `resume` の持ち主と操作節の分類

   関数の持ち主は、その関数の中の `resume` が再開する継続を受け取る操作節である。
   持ち主は次のとおりに決める。

   - 操作節の関数の持ち主は、その関数自身である。
   - ハンドラ式の本体(`handlebody`)の関数の持ち主は、そのハンドラ式を含む関数の持ち主である。
     ただし、操作節のガードのフィールドの中にあるハンドラ式の本体は、持ち主を持たない。
     ガードには `resume` を書けないからである。
   - それ以外の関数は持ち主を持たない。

   `handlebody` の関数から、それを作った関数を順にたどると、関数表の中で循環することがある。
   ルート関数から到達できない `handlebody` の関数が、ハンドラ式で自身を作る場合と、
   ほかの `handlebody` の関数と互いを順に作る場合である。
   循環する関数からたどっても `opclause` に到達しないので、その関数は持ち主を持たない。
   たどる途中で、たどっている最中の関数に戻れば、循環に入ったとわかる。
   そのとき、たどってきた関数はどれも持ち主を持たない。
   たどった関数の持ち主は表に記録し、次にその関数をたどるときは、
   記録した結果を使ってそこでたどるのをやめる。
   どの関数も 1 度しかたどらないので、`handlebody` の関数が長く連なっていても、
   たどる回数の合計は関数の個数に比例する。

   持ち主のない関数にある `resume` と、持ち主が N の操作節である関数にある `resume` は拒否する。
   操作節の分類は、その節を持ち主とする関数の `resume` の印をすべて集めて再計算する。
   `never` の印の付いた操作の節は N、すべての印が `tail` の節は T、それ以外の節は G である。
   `resume` を 1 つも持たない節は T になる。
   ハンドラ式の本体の中の `resume` は背骨の上にないので、印は `ntail` で、持ち主の節は G になる。 *)
type owner_memo = Walking | Done of string option

let owner env origins memo f =
  let rec walk path f =
    match Hashtbl.find_opt memo f with
    | Some (Done o) -> (o, path)
    | Some Walking -> (None, path)
    | None -> (
        let fn = get "関数" env.fns f in
        Hashtbl.replace memo f Walking;
        let path = f :: path in
        match (fn.f_kind, Hashtbl.find origins f) with
        | Opclause, _ -> (Some f, path)
        | Handlebody, Site { parent; in_guard = false; _ } -> walk path parent
        | _ -> (None, path))
  in
  let found, path = walk [] f in
  List.iter (fun g -> Hashtbl.replace memo g (Done found)) path;
  found

let check_classes env origins resumes =
  let owned = Hashtbl.create 64 in
  let memo = Hashtbl.create 64 in
  Hashtbl.iter
    (fun f rs ->
      if rs <> [] then
        match owner env origins memo f with
        | None -> fail "関数 %s: resume を書けない関数に resume があります" f
        | Some o -> Hashtbl.replace owned o (List.rev_append rs (Option.value ~default:[] (Hashtbl.find_opt owned o))))
    resumes;
  Hashtbl.iter
    (fun f o ->
      match o with
      | Site { h_op = Some (e, op, written); _ } ->
          let never = (op_of env e op).o_never in
          let rs = Option.value ~default:[] (Hashtbl.find_opt owned f) in
          if never && rs <> [] then fail "関数 %s: N の操作節に resume があります" f;
          let want = if never then N else if List.for_all Fun.id rs then T else G in
          if want <> written then fail "関数 %s: 操作節の分類 %s が、再計算した %s と違います" f (clause_class_name written) (clause_class_name want)
      | _ -> ())
    origins

(* ## 21.7 単位と初期化

   単位の並びは、`builtin`、`prelude` で始まり、`main` で終わる。
   `builtin` の単位は初期化手順を持たない。
   初期化手順は、組み込みでないグローバルをちょうど 1 回ずつ、
   インスタンスをちょうど 1 回ずつ定義する。
   初期化手順が定義するグローバルとインスタンスは、その初期化手順を持つ単位のものである。

   定義するグローバルの種類は、初期化手順ごとに決まっている。

   | 初期化手順 | 定義するグローバル |
   |---|---|
   | `def_value g f` | 種類 `value` の `g`。`f` の結果の Rep は `g` の Rep と同じ |
   | `def_pattern f gs p` | 種類 `value` の `gs`。`p` の `bind` は `gs` の位置を 0 から順に 1 回ずつ指す |
   | `def_fns gs` | 種類 `fn`、`dictabs`、`extern` の `gs`。`gs` は空でない |
   | `def_dictabs g` | 種類 `dictabs` の `g` |

   インスタンスは、クラスと対象の型が表にあり、
   メソッドの実装がクラスのメソッドと合わなければならない。
   インスタンスは、クラスの各メソッドの実装をちょうど 1 個ずつ持つ。
   言語はインスタンスの本体にクラスのすべてのメソッドを書くことを求めるからである。
   実装の順序は本体に書いた順で、クラスのメソッドの順序と同じでなくてよい。
   実装の項目に書く辞書の個数は、クラスのメソッドの辞書の個数と同じである。
   実装の関数が受け取る辞書の引数の個数は、インスタンスの前提の個数と、
   実装の項目に書いた辞書の個数の和である。 *)
let unit_table (p : program) =
  let keys = List.map (fun u -> u.u_key) p.units in
  let h = table "単位" Fun.id keys in
  (match keys with
   | "builtin" :: "prelude" :: rest when rest <> [] && List.nth rest (List.length rest - 1) = "main" -> ()
   | _ -> fail "単位の列が builtin、prelude で始まり main で終わる形になっていません");
  h

let check_units env (p : program) =
  (match p.units with u :: _ when u.u_init <> [] -> fail "builtin の単位が初期化の手順を持ちます" | _ -> ());
  let defined = Hashtbl.create 256 in
  let define u g ok what =
    let gl = get "大域" env.globals g in
    if not (ok gl.g_kind) then fail "大域 %s の種類が %s の手順と合いません" g what;
    if unit_of_symbol g <> u.u_key then fail "大域 %s を単位 %s の手順が定義します" g u.u_key;
    if Hashtbl.mem defined g then fail "大域 %s を 2 回定義します" g;
    Hashtbl.replace defined g ()
  in
  let thunk f = get "関数" env.fns f in
  let inst_defined = Hashtbl.create 64 in
  List.iter
    (fun u ->
      List.iter
        (function
          | Def_value (g, f) ->
              define u g (function GValue _ -> true | _ -> false) "def_value";
              (match (get "大域" env.globals g).g_kind with
               | GValue r -> if (thunk f).f_result <> r then fail "大域 %s の Rep が初期化の関数の結果の Rep と違います" g
               | _ -> ())
          | Def_pattern (_, gs, pat) ->
              List.iter (fun g -> define u g (function GValue _ -> true | _ -> false) "def_pattern") gs;
              let next = ref 0 in
              let rec go = function
                | PWild | PLit _ -> ()
                | PBind i ->
                    if i <> !next then fail "def_pattern のパターンの bind %d が大域の列の順と合いません" i;
                    incr next
                | PRecord (fs, tl) -> (
                    List.iter (fun (_, p) -> go p) fs;
                    match tl with Rest p -> go p | Closed | Open -> ())
                | PCtor (t, c, fs) ->
                    let ct = ctor_of env t c in
                    ignore (List.fold_left (fun prev (i, _) -> if i <= prev || i >= ct.ct_arity then fail "def_pattern のコンストラクタ %s のフィールドの位置が不正です" c else i) (-1) fs);
                    List.iter (fun (_, p) -> go p) fs
                | PVariant (_, p) -> go p
              in
              go pat;
              if !next <> List.length gs then fail "def_pattern のパターンが大域の列のすべてを束縛しません"
          | Def_fns gs ->
              if gs = [] then fail "def_fns の大域がありません";
              List.iter (fun g -> define u g (function GFn _ | GDictabs _ | GExtern _ -> true | _ -> false) "def_fns") gs
          | Def_dictabs g -> define u g (function GDictabs _ -> true | _ -> false) "def_dictabs"
          | Def_instance i ->
              ignore (get "インスタンス" env.instances i);
              if unit_of_symbol i <> u.u_key then fail "インスタンス %s を単位 %s の手順が定義します" i u.u_key;
              if Hashtbl.mem inst_defined i then fail "インスタンス %s を 2 回定義します" i;
              Hashtbl.replace inst_defined i ()
          | Run_exp _ -> ())
        u.u_init)
    p.units;
  List.iter
    (fun g ->
      match g.g_kind with
      | GBuiltin -> if Hashtbl.mem defined g.g_sym then fail "組み込みの大域 %s を手順が定義します" g.g_sym
      | _ -> if not (Hashtbl.mem defined g.g_sym) then fail "大域 %s を定義する手順がありません" g.g_sym)
    p.globals;
  List.iter (fun i -> if not (Hashtbl.mem inst_defined i.i_sym) then fail "インスタンス %s を定義する手順がありません" i.i_sym) p.instances

let check_instances env (p : program) =
  List.iter
    (fun i ->
      let cl = get "クラス" env.classes i.i_class in
      ignore (get "型" env.types i.i_head);
      unique "インスタンス" i.i_sym (List.map (fun (m, _, _) -> m) i.i_methods);
      List.iter
        (fun (m, k, f) ->
          (match List.assoc_opt m cl.c_methods with
           | Some k' -> if k <> k' then fail "インスタンス %s のメソッド %s の辞書の数がクラスと違います" i.i_sym m
           | None -> fail "インスタンス %s のメソッド %s がクラス %s にありません" i.i_sym m i.i_class);
          let fn = get "関数" env.fns f in
          if fn.f_dicts <> i.i_premises + k then fail "インスタンス %s のメソッド %s の実装の辞書の引数の数が違います" i.i_sym m)
        i.i_methods;
      List.iter
        (fun (m, _) ->
          if not (List.exists (fun (m', _, _) -> m' = m) i.i_methods) then
            fail "インスタンス %s がクラス %s のメソッド %s を実装しません" i.i_sym i.i_class m)
        cl.c_methods)
    p.instances

(* ## 21.8 組み込みの表と操作の印

   組み込みの型、クラス、値は、付録 A の項目を付録 A の順に、それぞれの表の先頭に置く。
   比較対象は第18章のライタが書く表そのものなので、ライタと検証が食い違うことはない。
   単位のキーが `builtin` の項目は、この先頭の部分以外には置けない。
   種類が `builtin` のグローバルも、先頭の部分以外には置けない。
   評価器は組み込みの値をシンボルで解決するので、付録 A にないシンボルの組み込みの値を受理すると、
   評価器がリンクのときにその名前を解決できずに失敗するからである。
   エフェクト表とインスタンス表には、単位のキーが `builtin` の項目を置けない。

   `runtime` の印は、プレリュードの `Console` の操作 `write` のうち引数が 1 個のものに付き、
   ほかの操作には付かない。
   この操作に印がない KIR も、ほかの操作に印がある KIR も拒否する。
   リーダは、この印の付いた操作の `perform` を、
   ハンドラを探さずにランタイムの書き込みとして実行してよい。
   そのため、印が付く操作を限らないと、リーダごとに動作が分かれる。
   同じ理由で、`runtime` の印の付いた操作を持つエフェクトを `handle` することもできない。
   この検査は §21.4 の `handle` の箇所で行い、
   印が付く操作の判定は §21.1 の `is_runtime_op` に置く。 *)
let check_builtins (p : program) =
  let is_builtin s = unit_of_symbol s = "builtin" in
  let rec prefix what eq want got =
    match (want, got) with
    | [], rest -> rest
    | w :: want, g :: got when eq w g -> prefix what eq want got
    | _ -> fail "%sの表の先頭が、付録 A の組み込みの%sの並びと合いません" (fst what) (snd what)
  in
  let rest_types = prefix ("型", "型") (fun w t -> t.t_sym = "builtin/" ^ w && t.t_ctors = []) Ir_write.builtin_types p.types in
  List.iter (fun t -> if is_builtin t.t_sym then fail "組み込みでない位置に組み込みの型 %s があります" t.t_sym) rest_types;
  let rest_classes =
    prefix ("クラス", "クラス") (fun (w, ms) c -> c.c_sym = "builtin/" ^ w && c.c_methods = List.map (fun m -> (m, 0)) ms) Ir_write.builtin_classes p.classes
  in
  List.iter (fun c -> if is_builtin c.c_sym then fail "組み込みでない位置に組み込みのクラス %s があります" c.c_sym) rest_classes;
  let rest_globals = prefix ("大域", "値") (fun w g -> g.g_sym = "builtin/" ^ w && g.g_kind = GBuiltin) Ir_write.builtin_values p.globals in
  List.iter
    (fun g -> if is_builtin g.g_sym || g.g_kind = GBuiltin then fail "組み込みでない位置に組み込みの値 %s があります" g.g_sym)
    rest_globals;
  List.iter (fun e -> if is_builtin e.e_sym then fail "単位 builtin のエフェクト %s があります" e.e_sym) p.effects;
  List.iter (fun i -> if is_builtin i.i_sym then fail "単位 builtin のインスタンス %s があります" i.i_sym) p.instances;
  List.iter
    (fun e ->
      List.iter
        (fun o ->
          if o.o_runtime <> is_runtime_op e o then
            fail "エフェクト %s の操作 %s の runtime の印が規則と合いません" e.e_sym o.o_name)
        e.e_ops)
    p.effects

(* ## 21.9 エントリポイント

   表を作り、単位の並び、シンボルの形式、名前の一意性、インスタンス、単位と初期化、
   組み込みの表と操作の印、関数の生成箇所、関数のフィールドと本体、操作節の分類の順に検査する。
   エラーは `Error` のメッセージにして返す。
   入れ子の上限で深さを抑えているので、
   `Stack_overflow` は、上限の深さに必要なスタックより小さいスタックでだけ起こる。
   そのときは `処理系の限度` のメッセージを返す。 *)
let check_exn ~max_nest (p : program) =
  let env =
    {
      types = table "型" (fun t -> t.t_sym) p.types;
      effects = table "エフェクト" (fun e -> e.e_sym) p.effects;
      classes = table "クラス" (fun c -> c.c_sym) p.classes;
      instances = table "インスタンス" (fun i -> i.i_sym) p.instances;
      globals = table "大域" (fun g -> g.g_sym) p.globals;
      fns = table "関数" (fun f -> f.f_sym) p.functions;
      max_nest;
    }
  in
  let units = unit_table p in
  let form what syms = List.iter (symbol_form units what) syms in
  form "型" (List.map (fun t -> t.t_sym) p.types);
  form "エフェクト" (List.map (fun e -> e.e_sym) p.effects);
  form "クラス" (List.map (fun c -> c.c_sym) p.classes);
  form "インスタンス" (List.map (fun i -> i.i_sym) p.instances);
  form "大域" (List.map (fun g -> g.g_sym) p.globals);
  form "関数" (List.map (fun f -> f.f_sym) p.functions);
  List.iter (fun t -> unique "型" t.t_sym (List.map (fun c -> c.ct_name) t.t_ctors)) p.types;
  List.iter (fun e -> unique "エフェクト" e.e_sym (List.map (fun o -> o.o_name) e.e_ops)) p.effects;
  List.iter (fun c -> unique "クラス" c.c_sym (List.map fst c.c_methods)) p.classes;
  check_instances env p;
  check_units env p;
  check_builtins p;
  let origins = origins p env in
  let resumes = Hashtbl.create 256 in
  List.iter (fun f -> Hashtbl.replace resumes f.f_sym (check_fn env origins f)) p.functions;
  check_classes env origins resumes

let check ?(max_nest = Ir_bin.max_nest) p =
  match check_exn ~max_nest p with
  | () -> Ok ()
  | exception Invalid msg -> Error msg
  | exception Stack_overflow -> Error "処理系の限度: KIR の検証でスタックが尽きました"
