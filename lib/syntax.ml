(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *)
open Aux

(* パス参照(型・パターン位置と、式位置の意味アクションが畳んだ結果)。
   成分は最後を除きすべて大文字識別子 *)
type long_id = LongId of string list

let long_id components = LongId components

let show_long_id (LongId components) = String.concat "." components

module Type = struct
  type level = int

  (* 名前インターン。record ラベル / エフェクト名 / 型構成子 / クラス名 / ctor 名 /
     識別子で共有する。名前空間の区別は使う側の文脈(表)が担う *)
  let intern_map : (string, oid) Hashtbl.t = Hashtbl.create 1024

  let name_map : (oid, string) Hashtbl.t = Hashtbl.create 1024

  let intern name =
    match Hashtbl.find_opt intern_map name with
    | Some oid -> oid
    | None ->
        let ret = new_oid () in
        Hashtbl.add intern_map name ret;
        Hashtbl.add name_map ret name;
        ret

  let name_of oid = Hashtbl.find name_map oid

  (* 旧名エイリアス *)
  let label_to_oid = intern

  let oid_to_label = name_of

  type kind =
    | KStar
    | KRow (* record / variant / effect 行で共通。分けない *)
    | KArrow of kind * kind (* F[_] *)
    | KVar of kind_ref (* D7。宣言終了時 KStar に既定化 *)

  and kind_ref = { k_id : oid; mutable k_link : kind option }

  (* 1パラメータクラスの制約集合(Integral / Fractional の予約述語を含む) *)
  type cls = oid list

  type var_info = { vid : oid; vlevel : level; vkind : kind; vcls : cls }

  type ty =
    | TCon of oid * ty list (* 名目/組込み構成子の飽和形 *)
    | TApp of ty * ty (* HKT。頭が型変数のときだけ現れる(repr が保証) *)
    | TArrow of ty * ty * ty (* 引数(_item 行の TRecord)* 返り値 * エフェクト行 *)
    | TRecord of ty
    | TVariant of ty (* 構造的ヴァリアント。行1個 *)
    | TRowEmpty
    | TRowExtend of oid * ty * ty (* label * field(エフェクトならラベル引数)* rest *)
    | TVar of tvar ref

  and tvar = Unbound of var_info | Link of ty | Generic of var_info | Rigid of var_info

  (* ---- kind ---- *)

  let rec kind_repr = function
    | KVar ({ k_link = Some k; _ } as r) ->
        let k' = kind_repr k in
        r.k_link <- Some k';
        k'
    | k -> k

  let new_kind_var () = KVar { k_id = new_oid (); k_link = None }

  (* arity 個の * を取る構成子カインド: k_arrow 1 = KArrow (KStar, KStar) *)
  let rec k_arrow arity = if arity = 0 then KStar else KArrow (KStar, k_arrow (arity - 1))

  (* 単一化しつつ一致するかを返す。KVar は相手に破壊的に張る *)
  let rec same_kind a b =
    match (kind_repr a, kind_repr b) with
    | KStar, KStar | KRow, KRow -> true
    | KArrow (a1, a2), KArrow (b1, b2) -> same_kind a1 b1 && same_kind a2 b2
    | KVar r1, KVar r2 when r1 == r2 -> true
    | KVar r, k | k, KVar r ->
        r.k_link <- Some k;
        true
    | _ -> false

  (* 宣言終了時: 未解決の KVar を KStar に既定化する(D7) *)
  let rec default_kind k =
    match kind_repr k with
    | KVar r -> r.k_link <- Some KStar
    | KArrow (a, b) ->
        default_kind a;
        default_kind b
    | KStar | KRow -> ()

  let show_kind k =
    match kind_repr k with
    | KStar -> "Type"
    | KRow -> "Row"
    | KArrow _ as k ->
        (* F[_] 形式: 引数の個数だけ _ を並べる *)
        let rec args = function KArrow (a, b) -> a :: args (kind_repr b) | _ -> [] in
        let n = List.length (args k) in
        "[" ^ String.concat ", " (List.init n (fun _ -> "_")) ^ "] Type"
    | KVar r -> "?k" ^ string_of_int r.k_id

  (* ---- ty ---- *)

  (* TApp の正規化: 頭が飽和形 TCon なら引数に畳む(MiniLang の tapp) *)
  let tapp f a = match f with TCon (c, args) -> TCon (c, args @ [ a ]) | f -> TApp (f, a)

  (* Link 連鎖の経路圧縮 + TApp の頭の再正規化。
     以降の全関数は「まず repr してから match」を鉄則にする *)
  let rec repr ty =
    match ty with
    | TVar ({ contents = Link t } as r) ->
        let t' = repr t in
        r := Link t';
        t'
    | TApp (f, a) ->
        let f' = repr f in
        (match f' with TCon (c, args) -> TCon (c, args @ [ a ]) | _ -> if f' == f then ty else TApp (f', a))
    | t -> t

  (* TApp 連鎖を (頭, 引数列) に分解 *)
  let rec app_spine ty =
    match repr ty with
    | TApp (f, a) ->
        let h, args = app_spine f in
        (h, args @ [ a ])
    | t -> (t, [])

  (* 行を (フィールド列, 尾部) に分解。尾部は TRowEmpty か TVar *)
  let rec row_fields ty =
    match repr ty with
    | TRowExtend (l, f, rest) ->
        let fs, tail = row_fields rest in
        ((l, f) :: fs, tail)
    | t -> ([], t)

  let row_tail_var ty = match snd (row_fields ty) with TVar r -> Some r | _ -> None

  (* a のフィールドを b の前に積む(splice)。a は閉じている前提(elab が検査) *)
  let rec row_append a b =
    match repr a with
    | TRowExtend (l, f, rest) -> TRowExtend (l, f, row_append rest b)
    | TRowEmpty -> b
    | t -> ( match repr b with TRowEmpty -> t | _ -> bug "row_append: open row on the left")

  let new_var ?(kind = KStar) ?(classes = []) level =
    TVar (ref (Unbound { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes }))

  let new_row_var level = new_var ~kind:KRow level

  let new_rigid ?(kind = KStar) level = TVar (ref (Rigid { vid = new_oid (); vlevel = level; vkind = kind; vcls = [] }))

  (* ---- 組み込み名(v0) ---- *)

  let l_item = intern "_item" (* タプルのラベル(§14 TODO への裁定) *)

  let t_boolean = TCon (intern "Boolean", [])

  let t_int32 = TCon (intern "Int32", [])

  let t_int64 = TCon (intern "Int64", [])

  let t_float64 = TCon (intern "Float64", [])

  let t_string = TCon (intern "String", [])

  let t_never = TCon (intern "Never", [])

  (* Unit は名目型ではなく空レコード(sample.kel:41,112)。
     プレリュードの型エイリアスとしてのみ名前を持つ *)
  let t_unit = TRecord TRowEmpty

  (* 予約クラス(D8)。ユーザ宣言は拒否、一般化せず既定値に落とす *)
  let cls_integral = intern "Integral"

  let cls_fractional = intern "Fractional"

  (* 操作なしの組み込みエフェクトラベル(宣言構文が無いので decls.ml が直接登録する) *)
  let eff_heap = intern "Heap"

  let eff_blocking = intern "Blocking"
end

(* ---- 数値リテラル(D13: 字句テキストをそのまま保持)---- *)

type num_suffix = NsInt of int | NsUInt of int | NsFloat of int (* i64 / u8 / f32 *)

type number = { n_text : string; n_is_float : bool; n_suffix : num_suffix option }

(* ---- 演算子(D9: 表は prims.ml に一枚だけ置き、elab と interp が共有する)---- *)

type bin_op = Add | Sub | Mul | Div | Eq | Ne | Lt | Le | Gt | Ge | And | Or

(* ---- 型パラメータ束縛子: A / h / F[_] / [A: Add + Mul] ---- *)

type type_param = {
  tp_name : string; (* 大文字/小文字どちらも可(リージョン変数 h 用) *)
  tp_arity : int; (* F[_] なら 1。0 ならカインドは KVar(使用位置から推論) *)
  tp_classes : long_id list;
}

module type Data = sig
  type t

  val allocate : Location.span -> t
end

module EmptyData : Data = struct
  type t = unit

  let allocate _ = ()
end

module Make (Data : Data) = struct
  (* ---- 型式 ---- *)

  type type_exp' =
    | EIdent of long_id (* 型変数・構成子・エイリアス・エフェクト名。区別は環境 *)
    | EApply of type_exp * type_exp list (* List[A] / F[A] *)
    | EArrow of type_exp list * type_exp * type_exp option (* (A, B) => C @ E。@ 省略は None *)
    | EBraceRow of brace_elem list * type_exp option (* { ... extends T }。要素の形で意味が決まる *)
    | EVariantCase of string * type_exp option (* #Foo(T) / #Foo *)
    | EUnion of type_exp list (* #A | #B | R / IoError | ParseError *)
    | EHole (* List[_] の穴(instance 頭・F[_] 束縛子) *)

  and type_exp = Data.t * type_exp'

  and brace_elem =
    | BField of string * type_exp (* x: Float64 / read: () => String *)
    | BLabel of long_id * type_exp list (* Print / Heap[h] / ReqId(エフェクト行・行 splice) *)

  (* ---- パターン ---- *)

  type pat' =
    | PWildcard
    | PVar of string
    | PBool of bool
    | PNumber of number
    | PText of string
    | PRecord of (string * pat) list * pat option
        (* レコード/タプル両用。第2要素: None = 閉じた行(タプルの arity 検査)、
           Some p = 尾部束縛(...rest)。開くだけなら Some PWildcard(レコードパターンの既定) *)
    | PCtor of long_id * ctor_arg_pat list (* 位置 / ラベル指定。handle 節の頭にも使う *)
    | PVariant of string * pat
    | PAnnot of pat * type_exp (* パラメータの型注釈 (p: Point) *)

  and pat = Data.t * pat'

  and ctor_arg_pat = { cap_label : string option; cap_pat : pat }

  (* ---- 式 ---- *)

  type exp' =
    | Bool of bool
    | Number of number
    | Text of string
    | Ident of long_id (* 変数・パス参照。裸の ctor も *)
    | Hole (* ??? *)
    | Apply of exp * exp (* 第2引数は常に引数レコード(D5) *)
    | Construct of long_id * ctor_arg list (* Some(1) / Cons(tail = t)。ラベル付き引数 *)
    | Variant of string * exp (* #Foo(e)。ペイロードは常に単値 *)
    | BinOp of exp * bin_op * exp (* D9: elab / interp が prims.ml の表を引く *)
    | Not of exp (* ! のみ *)
    | Lambda of lambda (* fn(x, y) => e *)
    | Let of let_binding * exp
    | LetRec of let_binding list * exp
    | Seq of exp list (* 式文の列。let を含むブロックは Let(b, 残り) の入れ子 *)
    | Match of exp * clause list (* 単一スクルティニ(D18) *)
    | RecordEmpty
    | RecordExtend of exp * string * exp (* (rest, label, value)。評価は value → rest の順(§8.3) *)
    | RecordUpdate of exp * string * exp (* {r with l = e}。物理フィールド順保持のため専用ノード *)
    | RecordRestriction of exp * string (* r \ l *)
    | RecordSelection of exp * string
    | Perform of long_id * exp (* perform print(msg)。解決済み完全名は resolved へ *)
    | Handle of exp * clause list (* 節は match と共通。分類は elab が行い resolved へ(§7.3) *)
    | Resume of exp option (* D19。resume() / resume(e)。引数は record_of_args を通さない *)
    | Run of string * exp (* run h { ... } *)

  and exp = Data.t * exp'

  and ctor_arg = { ca_label : string option; ca_exp : exp }

  and lambda = { l_params : pat list; l_body : exp }

  and clause' = { cl_pat : pat; cl_guard : exp option; cl_body : exp }

  and clause = Data.t * clause'

  and let_binding' = {
    lb_pub : bool;
    lb_name : pat; (* 関数定義なら PVar。値束縛はパターン可(match に脱糖) *)
    lb_tparams : type_param list; (* let f[A, E] の [A, E]。値束縛にも付けられる *)
    lb_params : pat list option; (* None = 値束縛。Some ps = 関数定義 *)
    lb_ret : type_exp option; (* : T *)
    lb_eff : type_exp option; (* @ E *)
    lb_body : exp;
  }

  and let_binding = Data.t * let_binding'

  (* ---- 宣言 ---- *)

  type type_alias' = {
    ta_pub : bool;
    ta_name : string;
    ta_params : type_param list;
    ta_kind : string option; (* : Type / : EffectRow。解釈は elab *)
    ta_body : type_exp;
  }

  type ctor_decl = { cd_name : string; cd_fields : field_decl list }

  and field_decl = { fd_label : string option; fd_ty : type_exp }

  type newtype_rhs = NtCtors of ctor_decl list (* Never は [] *) | NtHole (* = ??? *)

  type newtype' = { nt_pub : bool; nt_name : string; nt_params : type_param list; nt_rhs : newtype_rhs }

  type effect' = {
    ef_pub : bool;
    ef_name : string;
    ef_params : type_param list; (* Keleut にパラメータ構文は無い。非空は elab が拒否 *)
    ef_ops : (string * type_exp) list;
  }

  type class_val = { cv_name : string; cv_tparams : type_param list; cv_ty : type_exp }

  type class_decl' = {
    cls_pub : bool;
    cls_name : string;
    cls_params : type_param list; (* 1個であることは elab が検査(D11) *)
    cls_vals : class_val list;
    cls_derives : string list; (* derive structural *)
  }

  type extern_decl' = {
    ex_pub : bool;
    ex_abi : string; (* "prim" / "C" *)
    ex_name : string;
    ex_tparams : type_param list;
    ex_params : pat list;
    ex_ret : type_exp option;
    ex_eff : type_exp option;
  }

  type decl' =
    | DType of type_alias'
    | DNewtype of newtype'
    | DEffect of effect'
    | DClass of class_decl'
    | DInstance of instance_decl'
    | DLet of let_binding
    | DLetRec of let_binding list
    | DModule of bool * string * decl list (* pub * 名前 * 本体 *)
    | DExtern of extern_decl'
    | DExp of exp (* トップレベル式文(sample.kel:454) *)

  and decl = Data.t * decl'

  and instance_decl' = {
    ins_class : string;
    ins_args : type_exp list; (* 通常1個。List[_] の EHole 可 *)
    ins_body : decl list; (* let のみであることは elab が検査 *)
  }
end
