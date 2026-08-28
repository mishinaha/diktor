(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 型推論(計画 §7)。elab_type / elab_pat / elab_exp / elab_decl と2パスの宣言処理。
 * eff は下向きに渡し(MiniLang §11)、level は常に引数で渡す(R9)。
 * M4 スコープ: リテラル述語・レコード・タプル・注釈・値制限・演算子。
 * match/newtype は M5、エフェクトは M6、ユーザ宣言クラスは M7 で足す。
 *)
open Aux
open Syntax
open Type
module T = Tree.Tree
module SMap = Map.Make (String)

type env = {
  values : ty SMap.t;
  types : ty SMap.t; (* 型パラメータ束縛(リージョン変数 h を含む) *)
  resume_ty : ty option; (* ハンドラ操作節の中でのみ Some(M6) *)
}

let warnings : string list ref = ref []

let warn msg = warnings := !warnings @ [ msg ]

let closed_item_row tys = List.fold_right (fun t acc -> TRowExtend (l_item, t, acc)) tys TRowEmpty

(* 数値リテラルの型(D8, D13) *)
let number_ty level (n : number) : ty =
  match n.n_suffix with
  | Some (NsInt 32) -> t_int32
  | Some (NsInt 64) -> t_int64
  | Some (NsFloat 64) -> t_float64
  | Some _ -> type_error ("数値接尾辞 " ^ Lexer.show_number n ^ " は v0 では未対応です(i32/i64/f64 を使ってください)")
  | None ->
      let v = new_var level in
      Unify.add_class v (if n.n_is_float then cls_fractional else cls_integral);
      v

(* v0 で名前だけ受理して実行できない数値型(D13) *)
let unsupported_numeric = [ "Int8"; "Int16"; "UInt8"; "UInt16"; "UInt32"; "UInt64"; "Float32" ]

(* ---- 型式の elaboration ---- *)

(* expanding: エイリアス展開中集合(非再帰検査、§2.1) *)
let rec elab_type env level ~expanding ((_, te) : T.type_exp) : ty =
  match te with
  | T.EIdent (LongId [ n ]) -> (
      match SMap.find_opt n env.types with
      | Some t -> t
      | None ->
          if List.mem n unsupported_numeric then type_error ("数値型 " ^ n ^ " は v0 では未対応です(Int32/Int64/Float64 を使ってください)")
          else
            let oid = intern n in
            (match Hashtbl.find_opt Decls.aliases oid with
            | Some info -> expand_alias env level ~expanding info []
            | None ->
                if Hashtbl.mem Decls.con_kinds oid then (
                  match Decls.con_kind oid 0 with
                  | KStar -> TCon (oid, [])
                  | _ -> type_error ("型構成子 " ^ n ^ " には型引数が必要です"))
                else type_error ("未知の型: " ^ n)))
  | T.EIdent li -> type_error ("モジュール修飾の型参照は未対応です(M10): " ^ show_long_id li)
  | T.EApply ((_, T.EIdent (LongId [ n ])), args) -> (
      match SMap.find_opt n env.types with
      | Some t ->
          (* HKT 変数への適用。カインドは使用時に kind_of / drop_arrows が確定する *)
          List.fold_left (fun acc a -> tapp acc (elab_type env level ~expanding a)) t (List.map (fun a -> check_no_hole a) args)
      | None -> (
          let oid = intern n in
          match Hashtbl.find_opt Decls.aliases oid with
          | Some info -> expand_alias env level ~expanding info args
          | None ->
              if Hashtbl.mem Decls.con_kinds oid then (
                let k = Decls.con_kind oid (List.length args) in
                let rec arity k = match kind_repr k with KArrow (_, r) -> 1 + arity r | _ -> 0 in
                let expected = arity k in
                if expected <> List.length args then
                  type_error (Printf.sprintf "型構成子 %s の引数は %d 個必要です(%d 個与えられました)" n expected (List.length args))
                else TCon (oid, List.map (fun a -> elab_type env level ~expanding (check_no_hole a)) args))
              else type_error ("未知の型: " ^ n)))
  | T.EApply _ -> type_error "型適用の頭は型名でなければなりません"
  | T.EArrow (params, ret, eff_opt) ->
      let param_tys = List.map (elab_type env level ~expanding) params in
      let eff = match eff_opt with None -> new_row_var level | Some e -> elab_eff env level ~expanding e in
      TArrow (TRecord (closed_item_row param_tys), elab_type env level ~expanding ret, eff)
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            let tt = elab_type env level ~expanding t in
            match repr tt with
            | TRecord row -> row (* {x: T extends Point}: レコード型の行を splice *)
            | t' ->
                if Unify.kind_of t' = KRow || same_kind (Unify.kind_of t') KRow then t'
                else type_error "extends の右は行かレコード型でなければなりません")
      in
      let row =
        List.fold_right
          (fun elem acc ->
            match elem with
            | T.BField (l, t) -> TRowExtend (intern l, elab_type env level ~expanding t, acc)
            | T.BLabel _ -> type_error "エフェクトラベルはこの位置(レコード型)では使えません")
          elems tail
      in
      TRecord row
  | T.EVariantCase (s, payload) ->
      let pty = match payload with None -> t_unit | Some t -> elab_type env level ~expanding t in
      TVariant (TRowExtend (intern s, pty, TRowEmpty))
  | T.EUnion ts ->
      (* 各要素を行に落として連結(§7.3)。開いてよいのは末尾要素だけ *)
      let n = List.length ts in
      let rows =
        List.mapi
          (fun i t ->
            let is_last = i = n - 1 in
            match snd t with
            | T.EVariantCase (s, payload) ->
                let pty = match payload with None -> t_unit | Some t -> elab_type env level ~expanding t in
                TRowExtend (intern s, pty, TRowEmpty)
            | _ -> (
                let tt = elab_type env level ~expanding t in
                match repr tt with
                | TVariant row ->
                    let _, tail = row_fields row in
                    if (not is_last) && repr tail <> TRowEmpty then type_error "ヴァリアント和の途中の要素は閉じていなければなりません"
                    else row
                | t' ->
                    if same_kind (Unify.kind_of t') KRow then
                      if is_last then t' else type_error "ヴァリアント和の途中に行変数は置けません"
                    else type_error ("ヴァリアント和の要素になれない型です: " ^ Show.show t')))
          ts
      in
      let rec fold = function [] -> TRowEmpty | [ r ] -> r | r :: rest -> row_append r (fold rest) in
      TVariant (fold rows)
  | T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)"

and check_no_hole ((_, te) as t : T.type_exp) =
  match te with T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)" | _ -> t

and expand_alias env level ~expanding info args =
  if List.mem info.Decls.al_name expanding then
    type_error ("型エイリアス " ^ name_of info.Decls.al_name ^ " が再帰しています(エイリアスは非再帰)")
  else if List.length args <> List.length info.Decls.al_params then
    type_error
      (Printf.sprintf "型エイリアス %s の引数は %d 個必要です(%d 個与えられました。部分適用は禁止)" (name_of info.Decls.al_name)
         (List.length info.Decls.al_params) (List.length args))
  else
    let arg_tys = List.map (fun a -> elab_type env level ~expanding (check_no_hole a)) args in
    let types =
      List.fold_left2 (fun m tp t -> SMap.add tp.tp_name t m) SMap.empty info.Decls.al_params arg_tys
    in
    (* エイリアス本体は閉じている: 型パラメータだけが見える *)
    let env' = { env with types } in
    let expanding = info.Decls.al_name :: expanding in
    match info.Decls.al_kind with
    | Some "EffectRow" -> elab_eff env' level ~expanding info.Decls.al_body
    | _ -> elab_type env' level ~expanding info.Decls.al_body

(* エフェクト行位置の elaboration(§7.6)。M6 で effect 宣言表と接続する *)
and elab_eff env level ~expanding ((_, te) as t : T.type_exp) : ty =
  match te with
  | T.EIdent (LongId [ n ]) when SMap.mem n env.types ->
      let tv = SMap.find n env.types in
      if same_kind (Unify.kind_of tv) KRow then tv else type_error ("行カインドではない型パラメータです: " ^ n)
  | T.EIdent (LongId [ n ]) when Hashtbl.mem Decls.aliases (intern n) ->
      let info = Hashtbl.find Decls.aliases (intern n) in
      expand_alias env level ~expanding info []
  | T.EIdent (LongId [ n ]) ->
      (* @ Print = @ {Print} の略記。エフェクト名の実在検査は M6 で effect 表に接続 *)
      TRowExtend (intern n, t_unit, TRowEmpty)
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            let tt = elab_eff env level ~expanding t in
            if same_kind (Unify.kind_of tt) KRow then tt else type_error "extends の右は行でなければなりません")
      in
      List.fold_right
        (fun elem acc ->
          match elem with
          | T.BLabel (LongId [ n ], []) -> (
              match Hashtbl.find_opt Decls.aliases (intern n) with
              | Some info -> row_append (expand_alias env level ~expanding info []) acc (* 行 splice(§7.6) *)
              | None ->
                  if SMap.mem n env.types then
                    (* {E1, Print} のような行変数の合成は未対応(末尾 extends のみ) *)
                    type_error ("行変数 " ^ n ^ " は extends の位置にのみ書けます")
                  else TRowExtend (intern n, t_unit, acc))
          | T.BLabel (LongId [ n ], args) ->
              TRowExtend
                (intern n, (match args with [ a ] -> elab_type env level ~expanding a | _ -> type_error "エフェクトラベルの引数は1個までです"), acc)
          | T.BLabel (li, _) -> type_error ("モジュール修飾のエフェクトは未対応です(M10): " ^ show_long_id li)
          | T.BField (l, _) -> type_error ("エフェクト行にフィールド " ^ l ^ " は書けません"))
        elems tail
  | _ -> elab_type env level ~expanding t

let elab_type env level t = elab_type env level ~expanding:[] t

let elab_eff env level t = elab_eff env level ~expanding:[] t

(* ---- パターン(§7.3。単相束縛、MiniLang:1546-1570)---- *)

let rec elab_pat env level seen expected ((_, p) as node : T.pat) : env =
  let set t = Tree.set_ty node t in
  set expected;
  match p with
  | T.PWildcard -> env
  | T.PVar x ->
      if List.mem x !seen then type_error ("同じパターン内で変数 " ^ x ^ " が重複しています")
      else (
        seen := x :: !seen;
        { env with values = SMap.add x expected env.values })
  | T.PAnnot (sub, te) ->
      Unify.unify expected (elab_type env level te);
      elab_pat env level seen expected sub
  | T.PBool _ ->
      Unify.unify expected t_boolean;
      env
  | T.PText _ ->
      Unify.unify expected t_string;
      env
  | T.PNumber n ->
      Unify.unify expected (number_ty level n);
      env
  | T.PRecord (fields, rest) -> (
      let ftys = List.map (fun (l, _) -> (l, new_var level)) fields in
      match rest with
      | None ->
          (* 閉じた行(タプルの arity 検査) *)
          let row = List.fold_right (fun (l, t) acc -> TRowExtend (intern l, t, acc)) ftys TRowEmpty in
          Unify.unify expected (TRecord row);
          List.fold_left2 (fun env (_, sub) (_, t) -> elab_pat env level seen t sub) env fields ftys
      | Some rest_pat ->
          let tail = new_row_var level in
          let row = List.fold_right (fun (l, t) acc -> TRowExtend (intern l, t, acc)) ftys tail in
          Unify.unify expected (TRecord row);
          let env = List.fold_left2 (fun env (_, sub) (_, t) -> elab_pat env level seen t sub) env fields ftys in
          elab_pat env level seen (TRecord tail) rest_pat)
  | T.PCtor _ -> noimpl "コンストラクタパターン(M5)"
  | T.PVariant _ -> noimpl "ヴァリアントパターン(M5)" 

(* ---- 値制限(§7.2。ブロック(Seq/Let 連鎖)は保守的に非値)---- *)

let rec is_value ((_, e) : T.exp) =
  match e with
  | T.Bool _ | T.Number _ | T.Text _ | T.Ident _ | T.Hole | T.Lambda _ | T.RecordEmpty -> true
  | T.Variant (_, v) -> is_value v
  | T.Construct (_, args) -> List.for_all (fun a -> is_value a.T.ca_exp) args
  | T.RecordExtend (r, _, v) -> is_value r && is_value v
  | T.RecordRestriction (r, _) -> is_value r
  | _ -> false

(* ---- 式(§7.3)---- *)

let rec elab_exp env level eff ((_, e) as node : T.exp) : ty =
  let t = elab_exp' env level eff node e in
  Tree.set_ty node t;
  t

and elab_exp' env level eff node e =
  ignore node;
  match e with
  | T.Bool _ -> t_boolean
  | T.Text _ -> t_string
  | T.Number n -> number_ty level n
  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.values with
      | Some sch -> Unify.instantiate level sch
      | None -> (
          match li with
          | LongId comps when comps <> [] && String.length (List.nth comps (List.length comps - 1)) > 0 -> (
              let last = List.nth comps (List.length comps - 1) in
              if last.[0] >= 'A' && last.[0] <= 'Z' then noimpl ("コンストラクタ参照 " ^ name ^ "(M5)")
              else type_error ("未束縛の変数: " ^ name))
          | _ -> type_error ("未束縛の変数: " ^ name)))
  | T.Hole -> new_var level
  | T.Lambda { l_params; l_body } ->
      let param_tys = List.map (fun _ -> new_var level) l_params in
      let seen = ref [] in
      let env2 = List.fold_left2 (fun env p t -> elab_pat env level seen t p) env l_params param_tys in
      let body_eff = new_row_var level in
      let tr = elab_exp env2 level body_eff l_body in
      TArrow (TRecord (closed_item_row param_tys), tr, body_eff)
  | T.Apply (f, arg) ->
      let tf = elab_exp env level eff f in
      let ta = elab_exp env level eff arg in
      let tr = new_var level in
      (* 関数の行を呼び出し側の eff と単一化(MiniLang:1319-1324。既存バグ 0.2-4 の修正) *)
      Unify.unify tf (TArrow (ta, tr, eff));
      tr
  | T.BinOp (l, op, r) -> (
      let tl = elab_exp env level eff l in
      let tr = elab_exp env level eff r in
      match Prims.bin_op_sem op with
      | Prims.OpBool ->
          Unify.unify tl t_boolean;
          Unify.unify tr t_boolean;
          t_boolean
      | Prims.OpMethod (cls, m) | Prims.OpMethodNot (cls, m) ->
          let scheme = method_scheme cls m in
          let ret = new_var level in
          Unify.unify (Unify.instantiate level scheme) (TArrow (TRecord (closed_item_row [ tl; tr ]), ret, eff));
          ret)
  | T.Not e ->
      Unify.unify (elab_exp env level eff e) t_boolean;
      t_boolean
  | T.RecordEmpty -> t_unit
  | T.RecordExtend (rest, l, v) ->
      let tv = elab_exp env level eff v in
      let rest_row = new_row_var level in
      Unify.unify (elab_exp env level eff rest) (TRecord rest_row);
      TRecord (TRowExtend (intern l, tv, rest_row))
  | T.RecordSelection (r, l) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, tf, rest)));
      tf
  | T.RecordRestriction (r, l) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, tf, rest)));
      TRecord rest
  | T.RecordUpdate (r, l, v) ->
      (* 制限してから拡張と同じ型付け(§7.3)。フィールド型は変わってよい *)
      let told = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, told, rest)));
      TRecord (TRowExtend (intern l, elab_exp env level eff v, rest))
  | T.Variant (s, v) -> TVariant (TRowExtend (intern s, elab_exp env level eff v, new_row_var level))
  | T.Seq es ->
      let rec go = function
        | [] -> t_unit
        | [ last ] -> elab_exp env level eff last
        | s :: rest ->
            ignore (elab_exp env level eff s);
            go rest
      in
      go es
  | T.Let (b, body) ->
      let env2 = elab_binding env level eff b in
      elab_exp env2 level eff body
  | T.LetRec (bs, body) ->
      let env2 = elab_rec_bindings env level eff bs in
      elab_exp env2 level eff body
  | T.Match _ -> noimpl "match(M5)"
  | T.Construct _ -> noimpl "コンストラクタ(M5)"
  | T.Perform _ -> noimpl "perform(M6)"
  | T.Handle _ -> noimpl "handle(M6)"
  | T.Resume _ -> noimpl "resume(M6)"
  | T.Run _ -> noimpl "run(M6)"

and method_scheme cls m =
  match Decls.find_class (intern cls) with
  | Some ci -> (
      match List.assoc_opt m ci.Decls.ci_methods with
      | Some t -> t
      | None -> bug ("組み込みクラス " ^ cls ^ " にメソッド " ^ m ^ " がありません"))
  | None -> bug ("組み込みクラス " ^ cls ^ " が未登録です")

(* ---- let 束縛(§7.3)---- *)

(* 型パラメータ束縛子 → Rigid 変数。返り値は (名前, 変数, ref) の列 *)
and make_rigids level tparams =
  List.map
    (fun tp ->
      let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
      let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
      let r = ref (Rigid { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes }) in
      (tp.tp_name, TVar r, r))
    tparams

(* 束縛スコープを出るとき: この束縛の Rigid を Generic に書き換える(注釈の一般化)。
   Rigid の脱出は unify / occurs_adjust が検査済みなので安全 *)
and release_rigids rigids =
  List.iter
    (fun (_, _, r) ->
      match !r with
      | Rigid i ->
          default_kind i.vkind (* 未解決カインドは KStar に既定化(D7) *);
          r := Generic i
      | _ -> ())
    rigids

and elab_binding env level eff ((_, b) as node : T.let_binding) : env =
  let annotated = b.T.lb_tparams <> [] || b.T.lb_ret <> None || b.T.lb_eff <> None in
  let is_fun = b.T.lb_params <> None in
  let gen = is_fun || annotated || is_value b.T.lb_body in
  let lvl = if gen then level + 1 else level in
  let rigids = make_rigids lvl b.T.lb_tparams in
  let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
  let fn_ty =
    match b.T.lb_params with
    | Some params ->
        let seen = ref [] in
        let param_tys = List.map (fun _ -> new_var lvl) params in
        let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
        let fn_eff = match b.T.lb_eff with Some e -> elab_eff env_ty lvl e | None -> new_row_var lvl in
        let ret_ty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
        let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
        (try Unify.unify ret_ty body_ty
         with Type_error msg -> type_error ("注釈された返り値型を満たしません(" ^ msg ^ ")"));
        TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
    | None ->
        let vty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
        (* 値束縛は外側の eff で評価される *)
        let body_ty = elab_exp env_ty lvl eff b.T.lb_body in
        (try Unify.unify vty body_ty
         with Type_error msg when b.T.lb_ret <> None -> type_error ("注釈された型を満たしません(" ^ msg ^ ")"));
        vty
  in
  Tree.set_ty node fn_ty;
  match snd b.T.lb_name with
  | T.PVar x ->
      if gen then Unify.generalize level fn_ty;
      release_rigids rigids;
      { env with values = SMap.add x fn_ty env.values }
  | T.PWildcard ->
      if gen then Unify.generalize level fn_ty;
      release_rigids rigids;
      env
  | _ ->
      (* パターン束縛は単相(単一ケース match と同じ扱い、§6.4)。M5 で網羅性キューに載せる *)
      release_rigids rigids;
      let seen = ref [] in
      elab_pat env level seen fn_ty b.T.lb_name

and elab_rec_bindings env level eff bs : env =
  (* 事前割り当ての単相変数で束縛 → 本体推論 → unify → 一般化(既存バグ 0.2-5 の修正)。多相再帰不可 *)
  let lvl = level + 1 in
  let names =
    List.map
      (fun (_, b) ->
        match snd b.T.lb_name with
        | T.PVar x -> (x, new_var lvl)
        | _ -> type_error "let rec の束縛はパターンにできません")
      bs
  in
  let env_rec = { env with values = List.fold_left (fun m (x, t) -> SMap.add x t m) env.values names } in
  List.iter2
    (fun ((_, b) as bnode) (_, pre) ->
      let rigids = make_rigids lvl b.T.lb_tparams in
      let env_ty = { env_rec with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env_rec.types rigids } in
      let fn_ty =
        match b.T.lb_params with
        | Some params ->
            let seen = ref [] in
            let param_tys = List.map (fun _ -> new_var lvl) params in
            let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
            let fn_eff = match b.T.lb_eff with Some e -> elab_eff env_ty lvl e | None -> new_row_var lvl in
            let ret_ty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
            let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
            Unify.unify ret_ty body_ty;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None ->
            let vty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
            Unify.unify vty (elab_exp env_ty lvl eff b.T.lb_body);
            vty
      in
      Unify.unify pre fn_ty;
      Tree.set_ty bnode fn_ty;
      release_rigids rigids)
    bs names;
  List.iter (fun (_, t) -> Unify.generalize level t) names;
  { env with values = List.fold_left (fun m (x, t) -> SMap.add x t m) env.values names }

(* ---- 宣言(2パス、§7.2)---- *)

let toplevel_eff () =
  List.fold_right (fun n acc -> TRowExtend (intern n, t_unit, acc)) Prims.runtime_effects TRowEmpty

let initial_env () =
  {
    values = List.fold_left (fun m (n, t) -> SMap.add n t m) SMap.empty (Decls.builtin_values ());
    types = SMap.empty;
    resume_ty = None;
  }

(* 注釈が完全な let の署名を(本体を見ずに)構築する。前方参照用(§7.2) *)
let signature_of_binding env (b : T.let_binding') : ty option =
  let full_params =
    match b.T.lb_params with
    | None -> b.T.lb_ret <> None
    | Some ps -> List.for_all (fun (_, p) -> match p with T.PAnnot _ -> true | _ -> false) ps && b.T.lb_ret <> None
  in
  if not full_params then None
  else
    try
      let lvl = 1 in
      let rigids = make_rigids lvl b.T.lb_tparams in
      let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
      let ty =
        match b.T.lb_params with
        | Some ps ->
            let param_tys =
              List.map
                (fun (_, p) -> match p with T.PAnnot (_, te) -> elab_type env_ty lvl te | _ -> assert false)
                ps
            in
            let fn_eff = match b.T.lb_eff with Some e -> elab_eff env_ty lvl e | None -> new_row_var lvl in
            let ret_ty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> assert false in
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None -> ( match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> assert false)
      in
      Unify.generalize 0 ty;
      release_rigids rigids;
      Some ty
    with Type_error _ | NotImplemented _ -> None

let binding_name (b : T.let_binding') = match snd b.T.lb_name with T.PVar x -> Some x | _ -> None

(* 宣言列の型検査。出力行(name : type / ⚠)を返す。型エラーは最初の1つで Type_error *)
let type_check_decls decls =
  warnings := [];
  Unify.reset ();
  let out = ref [] in
  let emit s = out := !out @ [ s ] in
  let eff0 = toplevel_eff () in
  (* パス1: 型エイリアスの登録と、注釈が完全な let の署名登録 *)
  let env0 = initial_env () in
  let env =
    List.fold_left
      (fun env (_, d) ->
        match d with
        | T.DType t ->
            Decls.add_alias
              { Decls.al_name = intern t.T.ta_name; al_params = t.T.ta_params; al_kind = t.T.ta_kind; al_body = t.T.ta_body };
            env
        | T.DLet (_, b) -> (
            match (binding_name b, signature_of_binding env b) with
            | Some x, Some ty -> { env with values = SMap.add x ty env.values }
            | _ -> env)
        | T.DLetRec bs ->
            List.fold_left
              (fun env (_, b) ->
                match (binding_name b, signature_of_binding env b) with
                | Some x, Some ty -> { env with values = SMap.add x ty env.values }
                | _ -> env)
              env bs
        | _ -> env)
      env0 decls
  in
  (* パス2: 本体の推論(宣言順) *)
  let show_binding env (_, b) =
    match binding_name b with
    | Some x -> emit (x ^ " : " ^ Show.show (SMap.find x env.values))
    | None -> ()
  in
  let step env ((_, d) as node) =
    let wbefore = List.length !warnings in
    let env' =
      match d with
      | T.DType t ->
          (* 実在検査(未知の型・再帰・部分適用)をここで走らせる。結果は捨てる *)
          let info = Hashtbl.find Decls.aliases (intern t.T.ta_name) in
          let lvl = 1 in
          let rigids = make_rigids lvl info.Decls.al_params in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          ignore
            (match info.Decls.al_kind with
            | Some "EffectRow" -> elab_eff env_ty lvl info.Decls.al_body
            | _ -> elab_type env_ty lvl info.Decls.al_body);
          release_rigids rigids;
          env
      | T.DLet b ->
          let env' = elab_binding env 0 eff0 b in
          Unify.default_numerics () (* 表示前に述語つき弱変数を既定化する(D8) *);
          show_binding env' b;
          env'
      | T.DLetRec bs ->
          let env' = elab_rec_bindings env 0 eff0 bs in
          Unify.default_numerics ();
          List.iter (show_binding env') bs;
          env'
      | T.DExp e ->
          let t = elab_exp env 0 eff0 e in
          Unify.default_numerics ();
          emit ("_ : " ^ Show.show t);
          env
      | T.DExtern ex ->
          (* extern 宣言は署名のみ(実装は M8 の builtin 表) *)
          let lvl = 1 in
          let rigids = make_rigids lvl ex.T.ex_tparams in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          let seen = ref [] in
          let param_tys = List.map (fun _ -> new_var lvl) ex.T.ex_params in
          ignore (List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty ex.T.ex_params param_tys);
          let fn_eff = match ex.T.ex_eff with Some e -> elab_eff env_ty lvl e | None -> new_row_var lvl in
          let ret_ty = match ex.T.ex_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
          let ty = TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff) in
          Unify.generalize 0 ty;
          release_rigids rigids;
          emit (ex.T.ex_name ^ " : " ^ Show.show ty);
          { env with values = SMap.add ex.T.ex_name ty env.values }
      | T.DNewtype _ -> noimpl "newtype(M5)"
      | T.DEffect _ -> noimpl "effect 宣言(M6)"
      | T.DClass _ -> noimpl "type class 宣言(M7)"
      | T.DInstance _ -> noimpl "type instance 宣言(M7)"
      | T.DModule _ -> noimpl "module(M10)"
    in
    Unify.default_numerics ();
    (* この宣言で出た警告を出力に差し込む *)
    List.iteri (fun i w -> if i >= wbefore then emit ("⚠ " ^ w)) !warnings;
    ignore node;
    env'
  in
  let _env = List.fold_left step env decls in
  !out

let type_check decls =
  try Ok (type_check_decls decls) with
  | Type_error msg -> Error ("! 型エラー: " ^ msg)
  | Syntax_error msg -> Error ("! 構文エラー: " ^ msg)
