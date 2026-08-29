(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第4章 — AST を目で見る

   第3章 (parser.mly) は表面構文を畳んで AST を作りました。畳んだ結果が本当に
   意図どおりかを確かめる方法が要ります。このファイルはそのための道具で、
   `diktor --dump-ast FILE` が脱糖後の AST を S 式で標準出力に吐きます (計画 §8.7)。

   道具としては小さく、パイプラインの本線には入っていません。第16章 (driver.ml) は
   `--dump-ast` のときパースだけして、ここに渡し、elab を呼ばずに終わります。
   だから**このダンプに型は出ません**。まだ書かれていないからです (第5章 tree.ml の
   `ty_field` は `None` のまま)。型が見たいときは第9章 (show.ml) と型検査の経路が別にあります。

   ここに書いてあるのは2つです。

   - S 式にする写像 — AST のコンストラクタひとつひとつに、短い名前を1個ずつ割り当てる
   - その読み方 — 第3章の脱糖表 (計画 §6.4) を、出力から逆に読む手順 (§4.2)

   ppx (`deriving show` の類) を入れずに手で書いているのは、依存を増やさないためです。
   Diktor の依存は menhir と sedlex の2つだけ (D15) で、それは
   「教材として最初から最後まで読める」ことと同じ目標から来ています。
   コンストラクタの数だけ手で書く退屈さは、依存 1 個ぶんの価値がある、という判断です。

   ### 前章から受け取るもの

   - 第3章が作った脱糖済みの `decl list`。注釈 (位置と、まだ空の型欄) は使いません

   ### 誰にも渡さないもの

   - 出力は人間の目と、`test/ast.t` の cram ゴールデンだけが読みます。
     読み戻す機能はありません (§4.2) *)
open Syntax
open Tree.Tree

(* ## 4.1 S 式は2つのコンストラクタで足りる

   原子 (`A`) と括弧 (`L`) だけです。属性も、位置も、型も持ちません。
   S 式を選んだ理由は、括弧の対応さえ合っていれば人間が木構造を追えることと、
   1 行の diff がそのまま「木のどこが変わったか」になることです。

   整形は `Format` に任せます。`hov` ボックスにインデント 1 を与えているので、
   端末幅で折り返しても、続きの要素が開き括弧の直後の桁に揃います。要素の区切りに
   `@ ` を使っているのが肝で、これは「ここは空白 1 個、ただし詰まっていれば
   ここで改行してよい」という指示です。空白を直接書くと折り返しが起きず、
   深い木が 1 行に伸びて読めなくなります。

   > 木を見せる道具は、折り返しの位置を自分で決めてはいけない。幅を知っているのは端末だけ。 *)
type sexp = A of string | L of sexp list

let rec pp fmt = function
  | A s -> Format.pp_print_string fmt s
  | L xs ->
      Format.fprintf fmt "@[<hov 1>(";
      List.iteri
        (fun i x ->
          if i > 0 then Format.fprintf fmt "@ ";
          pp fmt x)
        xs;
      Format.fprintf fmt ")@]"

(* ## 4.2 出力の読み方 — 脱糖を目で確かめる

   ここからが、この章の教材としての本題です。使い方は3手あります。

   1. 表面構文を1行書く
   2. 第3章のどの脱糖が効くはずかを、**先に頭の中で言う**
   3. `--dump-ast` の出力と突き合わせる

   3 で食い違ったときは、たいてい 2 のほうが間違っています。脱糖の規約は
   §3.5 の「arity 1 の3規約」のように互いに噛み合っていて、記憶で書くと1つずれます。

   代表的な対応表です (実際のゴールデンは `test/ast.t` にあります)。

   | 書いたもの | ダンプ | 確かめていること |
   |---|---|---|
   | `(1, 2)` | `(extend _item 1 (extend _item 2 {}))` | タプルは `_item` の重複行 |
   | `(1)` | `1` | 式の括弧はグループ化 (§3.5) |
   | `(1,)` | `(extend _item 1 {})` | 1-タプルはカンマで作る |
   | `f(1, 2)` | `(apply f (extend _item 1 (extend _item 2 {})))` | 引数も同じ行 (D5) |
   | `t._1` | `(select _item (restrict _item t))` | 剥がしてから選ぶ (§3.4) |
   | `{x, y}` | `(extend x x (extend y y {}))` | パンニング |
   | `{r with x = 3}` | `(update x 3 r)` | 更新は脱糖しない (§3.20) |
   | `#Point(1, 2)` | `(#Point (extend _item 1 (extend _item 2 {})))` | 2引数はタプル |
   | `#Empty` | `(#Empty {})` | 引数なしは Unit ペイロード |
   | `Some(1)` | `(construct Some 1)` | コンストラクタの引数は畳まない (§3.6) |
   | `Parser.bind(p)` | `(apply Parser.bind (extend _item p {}))` | 小文字終端は適用 |
   | `Parser.Parser(g)` | `(construct Parser.Parser g)` | 大文字終端は構築 |

   最後の3行が並ぶと、§3.6 の裁定が目で見えます。`apply` の第2引数は必ず行ですが、
   `construct` の引数は生のまま並びます。ラベル付き引数を宣言順へ並べ替えるのは
   第11章の仕事なので、パーサは畳まずに渡している — その分担が、括弧の形の差として
   そのまま出力に現れているわけです。

   `with` の糖衣 (§3.8) は、ダンプで見るといちばん納得できます。

   ```
   let f = fn() => {
     with x = bind(p)
     pure(x)
   }
   ```

   のダンプは、およそこう出ます。

   ```
   (dlet
    (binding f =
     (fn ()
      (apply bind
       (extend _item p
        (extend _item (fn (x) (apply pure (extend _item x {}))) {}))))))
   ```

   継続 `fn (x) ...` が `bind` の**引数行のいちばん内側**、つまり最後の引数に
   入っていること、そして元の `p` が外側に残っていることが読み取れれば、
   `with_splice` の再帰が何をしたかを理解したことになります。

   ゴールデンは cram で固定してあります (実装記録 260829-2 の乖離6)。
   `test/ast.t` には sample.kel 全文のダンプ行数まで書いてあるので、文法や脱糖を
   変えると必ず差分が出ます。差分が出たら `dune promote` で更新できますが、
   **更新する前に目で見ること** — このゴールデンは第3章の設計判断そのものの写しです。

   なお、このダンプは読み戻せません。原子は生のまま出しますし、位置も型も落とします。
   唯一のエスケープが下の `quoted` で、テキストリテラルだけ `String.escaped` を通します。
   数値は第2章 (lexer.ml) の `show_number` を借りるので、桁区切りも接尾辞も
   `--dump-tokens` と同じ見え方になります。2つのダンプが食い違わないのは、
   表記を復元する関数が1つしかないからです。 *)
let show_bin_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | And -> "&&"
  | Or -> "||"

let quoted s = "\"" ^ String.escaped s ^ "\""

(* ## 4.3 型のダンプ

   型式は第3章がほとんど畳まずに運んできた形そのままです。だからダンプもほぼ 1 対 1 で、
   ここで確かめられるのは「畳まれた3か所」だけです。

   - `EBraceRow` は `row` として出ます。レコード型 `{x: Int32}` も
     エフェクト行 `{Print, Log}` も同じ `row` になり、フィールドは `x:` 付き、
     エフェクトラベルは裸で並びます — §3.23 で1本に統合した非終端の姿がそのまま見えます
   - 型位置の `(A)` は `(row (_item: A))` になります。式と違って常に1-タプルです (§3.20)
   - `#Foo(A, B)` はペイロードが `(row (_item: A) (_item: B))` に畳まれています

   `tapp` は `EApply`、`=>` は矢印で、エフェクト行があるときだけ `@` が後ろに付きます。
   `_` は `EHole` — 型引数に書いた `_` です。

   `sexp_of_tparam` は型パラメータ束縛子で、`F[_]` のときだけ `arity=1` が付き、
   クラス制約があるときだけ `:` で始まるリストになります (§3.17)。
   束縛子は「名前だけ」であることが多いので、既定を裸の原子にして、
   情報がある場合だけ括弧に昇格させています。ダンプ全体がこの方針です —
   **既定値は出さない**。出ているものだけが意味を持ちます。 *)
let sexp_of_tparam { tp_name; tp_arity; tp_classes } =
  let name = if tp_arity = 0 then A tp_name else L [ A tp_name; A (Printf.sprintf "arity=%d" tp_arity) ] in
  match tp_classes with
  | [] -> name
  | cs -> L (A ":" :: name :: List.map (fun c -> A (show_long_id c)) cs)

let rec sexp_of_ty (_, t) =
  match t with
  | EIdent li -> A (show_long_id li)
  | EApply (f, args) -> L (A "tapp" :: sexp_of_ty f :: List.map sexp_of_ty args)
  | EArrow (params, ret, eff) ->
      let base = [ A "=>"; L (List.map sexp_of_ty params); sexp_of_ty ret ] in
      L (match eff with None -> base | Some e -> base @ [ A "@"; sexp_of_ty e ])
  | EBraceRow (elems, ext) ->
      let elem = function
        | BField (l, t) -> L [ A (l ^ ":"); sexp_of_ty t ]
        | BLabel (li, []) -> A (show_long_id li)
        | BLabel (li, args) -> L (A (show_long_id li) :: List.map sexp_of_ty args)
      in
      let base = A "row" :: List.map elem elems in
      L (match ext with None -> base | Some t -> base @ [ A "extends"; sexp_of_ty t ])
  | EVariantCase (s, None) -> A ("#" ^ s)
  | EVariantCase (s, Some t) -> L [ A ("#" ^ s); sexp_of_ty t ]
  | EUnion ts -> L (A "union" :: List.map sexp_of_ty ts)
  | EHole -> A "_"

(* ## 4.4 パターンのダンプ

   パターンで目を凝らすべきは1点、**行が開いているか閉じているか**です (§3.9)。

   `precord` の末尾に `...` と、そのあとの尾部パターンが付いていたら開いた行です。
   レコードパターン `{x}` は第3章が尾部に `PWildcard` を必ず置くので、
   ダンプでは `(precord (x= x) ... _)` のように、書いた覚えのない `_` が現れます。
   これは間違いではなく、「書いていないフィールドは無視する」という既定の姿です。

   タプルパターンには `...` が付きません。`(precord (_item= x) (_item= y))` —
   尾部が無い、すなわち閉じた行で、要素数がぴったり合うことを単一化が要求します。
   第10章 (exhaust.ml) の網羅性検査がタプルとレコードで違う振る舞いをするのは、
   この `...` の有無を受け取っているからです。

   `pctor` はコンストラクタパターン。ラベル付きの引数は `l=` を頭に付けた括弧になり、
   `sexp_of_ctor_arg_pat` がその分岐だけを担当します。式側の `sexp_of_ctor_arg` と
   同じ形なのは、`Construct` と `PCtor` が同じラベル解決 (第11章の `RCtor` /
   `RCtorPat`) を受けるからです。 *)
let rec sexp_of_pat (_, p) =
  match p with
  | PWildcard -> A "_"
  | PVar x -> A x
  | PBool b -> A (string_of_bool b)
  | PNumber n -> A (Lexer.show_number n)
  | PText s -> A (quoted s)
  | PRecord (fields, rest) ->
      let f (l, p) = L [ A (l ^ "="); sexp_of_pat p ] in
      let base = A "precord" :: List.map f fields in
      L (match rest with None -> base | Some r -> base @ [ A "..."; sexp_of_pat r ])
  | PCtor (li, args) -> L (A "pctor" :: A (show_long_id li) :: List.map sexp_of_ctor_arg_pat args)
  | PVariant (s, p) -> L [ A ("#" ^ s); sexp_of_pat p ]
  | PAnnot (p, t) -> L [ A "pannot"; sexp_of_pat p; sexp_of_ty t ]

and sexp_of_ctor_arg_pat { cap_label; cap_pat } =
  match cap_label with None -> sexp_of_pat cap_pat | Some l -> L [ A (l ^ "="); sexp_of_pat cap_pat ]

(* ## 4.5 式のダンプ

   §4.2 の表がそのまま出てくる場所です。名前の付け方だけ補足します。

   レコードの4操作は `extend` / `update` / `restrict` / `select` で、
   引数の順は**ラベルを先、対象の行を後**に固定しました。`(extend x 1 (extend y 2 {}))` は
   書いた順に左から読め、いちばん右の `{}` が行の底になります。
   AST の `RecordExtend (rest, l, v)` とは引数の順が違いますが、これは意図的です —
   データ構造は「残りの行 + 1 枚」で組むのが自然で、読むときは「何のラベルか」を
   先に知りたいからです。

   `seq` は、1 つのブロックの文の並びからは平らに出ます — 第3章の
   `block_of_items` が自分の畳み込みでは入れ子を作らないからです (§3.7)。
   ただし**非末尾の文として書いた入れ子ブロック**はそのまま `seq` の中の
   `seq` として現れます(`{ 1; { 2; 3 }; 4 }` の類。末尾位置の入れ子だけは
   末尾の式がブロックの値になる規則で吸収されて平らになります)。
   `let` が右へ深くなるのはスコープの形そのものです。ブロックのダンプを見ると、
   `let` の連なりが右下がりの階段になり、その各段の右側がスコープの範囲になります。
   これは Keleut の `{ }` が「宣言の列」ではなく「入れ子の `Let`」であることの絵です。

   `resume` は引数ゼロなら `(resume)`、値付きなら `(resume e)` (§3.19)。
   `???` は `Hole` — 未実装の穴で、型検査は通り実行時に落ちます。

   `sexp_of_binding` は束縛の全情報を並べます。`(params ...)` が**あるかどうか**が
   関数形とパターン束縛形の違いで (§3.16)、`binding-pub` というタグが `pub` の有無です。
   型パラメータ・返り値注釈・エフェクト注釈も、書かれているときだけ現れます。
   ここでも既定は出しません。 *)
let rec sexp_of_exp (_, e) =
  match e with
  | Bool b -> A (string_of_bool b)
  | Number n -> A (Lexer.show_number n)
  | Text s -> A (quoted s)
  | Ident li -> A (show_long_id li)
  | Hole -> A "???"
  | Apply (f, a) -> L [ A "apply"; sexp_of_exp f; sexp_of_exp a ]
  | Construct (li, args) -> L (A "construct" :: A (show_long_id li) :: List.map sexp_of_ctor_arg args)
  | Variant (s, e) -> L [ A ("#" ^ s); sexp_of_exp e ]
  | BinOp (l, op, r) -> L [ A (show_bin_op op); sexp_of_exp l; sexp_of_exp r ]
  | Not e -> L [ A "!"; sexp_of_exp e ]
  | Lambda { l_params; l_body } -> L [ A "fn"; L (List.map sexp_of_pat l_params); sexp_of_exp l_body ]
  | Let (b, e) -> L [ A "let"; sexp_of_binding b; sexp_of_exp e ]
  | LetRec (bs, e) -> L [ A "letrec"; L (List.map sexp_of_binding bs); sexp_of_exp e ]
  | Seq es -> L (A "seq" :: List.map sexp_of_exp es)
  | Match (e, cs) -> L (A "match" :: sexp_of_exp e :: List.map sexp_of_clause cs)
  | RecordEmpty -> A "{}"
  | RecordExtend (rest, l, v) -> L [ A "extend"; A l; sexp_of_exp v; sexp_of_exp rest ]
  | RecordUpdate (r, l, v) -> L [ A "update"; A l; sexp_of_exp v; sexp_of_exp r ]
  | RecordRestriction (r, l) -> L [ A "restrict"; A l; sexp_of_exp r ]
  | RecordSelection (r, l) -> L [ A "select"; A l; sexp_of_exp r ]
  | Perform (li, args) -> L [ A "perform"; A (show_long_id li); sexp_of_exp args ]
  | Handle (e, cs) -> L (A "handle" :: sexp_of_exp e :: List.map sexp_of_clause cs)
  | Resume None -> L [ A "resume" ]
  | Resume (Some e) -> L [ A "resume"; sexp_of_exp e ]
  | Run (h, e) -> L [ A "run"; A h; sexp_of_exp e ]

and sexp_of_ctor_arg { ca_label; ca_exp } =
  match ca_label with None -> sexp_of_exp ca_exp | Some l -> L [ A (l ^ "="); sexp_of_exp ca_exp ]

and sexp_of_clause (_, { cl_pat; cl_guard; cl_body }) =
  let base = [ A "case"; sexp_of_pat cl_pat ] in
  let base = match cl_guard with None -> base | Some g -> base @ [ A "if"; sexp_of_exp g ] in
  L (base @ [ A "=>"; sexp_of_exp cl_body ])

and sexp_of_binding (_, b) =
  let tag = if b.lb_pub then "binding-pub" else "binding" in
  let base = [ A tag; sexp_of_pat b.lb_name ] in
  let base = match b.lb_tparams with [] -> base | ts -> base @ [ L (A "tparams" :: List.map sexp_of_tparam ts) ] in
  let base =
    match b.lb_params with None -> base | Some ps -> base @ [ L (A "params" :: List.map sexp_of_pat ps) ]
  in
  let base = match b.lb_ret with None -> base | Some t -> base @ [ A ":"; sexp_of_ty t ] in
  let base = match b.lb_eff with None -> base | Some t -> base @ [ A "@"; sexp_of_ty t ] in
  L (base @ [ A "="; sexp_of_exp b.lb_body ])

(* ## 4.6 宣言のダンプ

   宣言はダンプで見ると平板です。第3章がほとんど脱糖しないからで、計画 §6.4 の表のうち
   ここで確かめられるのは `newtype` の短縮形1件だけになります。

   - `newtype UserId(Int32)` が `(newtype UserId (UserId Int32))` になっている —
     短縮形がコンストラクタ1個に展開され、その名前が型名と同じであること (§3.10)

   表のもう1件、`let {x, y} = p` のパターン束縛はここには出ません。単一ケース match への
   脱糖がパーサでなく第11章 (elab.ml) 側に移ったからです (実装記録 260829-2 の乖離7)。

   脱糖ではありませんが、ついでに目で見えるものがもう1つあります。`pub` の有無が
   `-pub` 付きのタグになることです。これは計画 §6.4 の表の項目ではなく、`set_pub` が
   被せる修飾子 (§3.10) がそのままタグに出ているだけです。

   残りは形の確認です。`class` は `val` と `derive` を並べ、`instance` は
   クラス名・型引数・本体の宣言列を並べます。`instance` の本体が `dlet` の列に
   なっているのは、第3章が `items` を共有している (§3.15) ことの現れです。

   `sexp_of_decl` が再帰なのは `module` と `instance` が宣言を含むからで、
   その入れ子は第11章の `flatten_modules` が平らにする前の姿です。
   つまりこのダンプは**平坦化前**を見せます — module の入れ子がどう畳まれるかを
   知りたいときは、ここではなく第11章を読むことになります。

   最後に運用上の注意を1つ。`lib/dune` は Warning 8 (非網羅 match) を有効なまま
   残しています。AST にコンストラクタを1つ足すと、このファイルの `match` が警告を出して
   知らせてくれる — ダンパが構文から静かに取り残されない仕掛けです。
   ただし `warn-error` に含まれていないのでビルドは通ります。
   **警告を見る運用とセットで初めて効く**仕掛けだ、と正直に書いておきます。 *)
let sexp_of_ctor_decl { cd_name; cd_fields } =
  let f { fd_label; fd_ty } =
    match fd_label with None -> sexp_of_ty fd_ty | Some l -> L [ A (l ^ ":"); sexp_of_ty fd_ty ]
  in
  L (A cd_name :: List.map f cd_fields)

let rec sexp_of_decl (_, d) =
  match d with
  | DType t ->
      let base = [ A (if t.ta_pub then "type-pub" else "type"); A t.ta_name ] in
      let base = match t.ta_params with [] -> base | ps -> base @ [ L (List.map sexp_of_tparam ps) ] in
      let base = match t.ta_kind with None -> base | Some k -> base @ [ A (": " ^ k) ] in
      L (base @ [ A "="; sexp_of_ty t.ta_body ])
  | DNewtype n ->
      let base = [ A (if n.nt_pub then "newtype-pub" else "newtype"); A n.nt_name ] in
      let base = match n.nt_params with [] -> base | ps -> base @ [ L (List.map sexp_of_tparam ps) ] in
      let rhs = match n.nt_rhs with NtHole -> [ A "???" ] | NtCtors cs -> List.map sexp_of_ctor_decl cs in
      L (base @ rhs)
  | DEffect e ->
      let base = [ A (if e.ef_pub then "effect-pub" else "effect"); A e.ef_name ] in
      let base = match e.ef_params with [] -> base | ps -> base @ [ L (List.map sexp_of_tparam ps) ] in
      L (base @ List.map (fun (op, t) -> L [ A (op ^ ":"); sexp_of_ty t ]) e.ef_ops)
  | DClass c ->
      let base = [ A (if c.cls_pub then "class-pub" else "class"); A c.cls_name ] in
      let base = base @ [ L (List.map sexp_of_tparam c.cls_params) ] in
      let vals =
        List.map
          (fun v ->
            let vb = [ A "val"; A v.cv_name ] in
            let vb = match v.cv_tparams with [] -> vb | ts -> vb @ [ L (List.map sexp_of_tparam ts) ] in
            L (vb @ [ A ":"; sexp_of_ty v.cv_ty ]))
          c.cls_vals
      in
      let derives = List.map (fun d -> L [ A "derive"; A d ]) c.cls_derives in
      L (base @ vals @ derives)
  | DInstance i ->
      L
        (A "instance" :: A i.ins_class
        :: L (List.map sexp_of_ty i.ins_args)
        :: List.map sexp_of_decl i.ins_body)
  | DLet b -> L [ A "dlet"; sexp_of_binding b ]
  | DLetRec bs -> L (A "dletrec" :: List.map sexp_of_binding bs)
  | DModule (pub, name, ds) ->
      L (A (if pub then "module-pub" else "module") :: A name :: List.map sexp_of_decl ds)
  | DExtern e ->
      let base = [ A (if e.ex_pub then "extern-pub" else "extern"); A (quoted e.ex_abi); A e.ex_name ] in
      let base = match e.ex_tparams with [] -> base | ts -> base @ [ L (A "tparams" :: List.map sexp_of_tparam ts) ] in
      let base = base @ [ L (A "params" :: List.map sexp_of_pat e.ex_params) ] in
      let base = match e.ex_ret with None -> base | Some t -> base @ [ A ":"; sexp_of_ty t ] in
      let base = match e.ex_eff with None -> base | Some t -> base @ [ A "@"; sexp_of_ty t ] in
      L base
  | DExp e -> L [ A "exp"; sexp_of_exp e ]

(* ## 4.7 出力の口

   宣言 1 個につき 1 回 `%a@.` で書きます。`@.` は「改行してフラッシュ」なので、
   宣言の境目でボックスが必ず閉じ、次の宣言が新しい行から始まります。
   ゴールデンの diff を宣言単位に保つための、小さいけれど大事な選択です
   (`@\n` にすると前の宣言の折り返しに引きずられます)。

   最後の `pp_print_flush` は、`Format` の内部バッファに残った分を出し切るためのものです。
   これを忘れると、末尾の宣言が出ないまま終わることがあります — 標準出力の
   バッファリングとは別に、`Format` 自身がバッファを持っているからです。 *)
let dump_decls out decls =
  let fmt = Format.formatter_of_out_channel out in
  List.iter (fun d -> Format.fprintf fmt "%a@." pp (sexp_of_decl d)) decls;
  Format.pp_print_flush fmt ()
