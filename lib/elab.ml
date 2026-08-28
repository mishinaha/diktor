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
  resume_ty : (ty * ty) option; (* (操作の返り値型, handle 式全体の型)。操作節の中でのみ Some(§7.3) *)
}

let warnings : string list ref = ref []

let warn msg = warnings := !warnings @ [ msg ]

(* 型エラーで打ち切られるまでの出力行(driver がエラー時にも印字する) *)
let current_out : string list ref = ref []

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
      if info.Decls.al_kind = Some "EffectRow" then expand_alias env level ~expanding info []
      else type_error ("エフェクト位置に Type エイリアス " ^ n ^ " は使えません(: EffectRow を付けてください)")
  | T.EIdent (LongId [ n ]) ->
      (* @ Print = @ {Print} の略記(§7.6) *)
      if Hashtbl.mem Decls.effects (intern n) then TRowExtend (intern n, t_unit, TRowEmpty)
      else type_error ("未知のエフェクト: " ^ n)
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
              | Some info when info.Decls.al_kind = Some "EffectRow" ->
                  row_append (expand_alias env level ~expanding info []) acc (* 行 splice(§7.6) *)
              | Some _ -> type_error ("エフェクト行に Type エイリアス " ^ n ^ " は置けません(: EffectRow を付けてください)")
              | None ->
                  if SMap.mem n env.types then
                    (* {E1, Print} のような行変数の合成は未対応(末尾 extends のみ) *)
                    type_error ("行変数 " ^ n ^ " は extends の位置にのみ書けます")
                  else if Hashtbl.mem Decls.effects (intern n) then TRowExtend (intern n, t_unit, acc)
                  else type_error ("未知のエフェクト: " ^ n))
          | T.BLabel (LongId [ n ], args) ->
              if not (Hashtbl.mem Decls.effects (intern n)) then type_error ("未知のエフェクト: " ^ n)
              else
                TRowExtend
                  ( intern n,
                    (match args with
                    | [ a ] -> elab_type env level ~expanding a
                    | _ -> type_error "エフェクトラベルの引数は1個までです"),
                    acc )
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
  | T.PVariant (str, sub) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify expected (TVariant (TRowExtend (intern str, tf, rest)));
      elab_pat env level seen tf sub
  | T.PCtor (li, args) -> (
      let (LongId comps) = li in
      let cname = List.nth comps (List.length comps - 1) in
      if not (cname.[0] >= 'A' && cname.[0] <= 'Z') then
        type_error ("未知のコンストラクタパターン: " ^ show_long_id li ^ "(操作節は handle の中でのみ使えます)")
      else
        match Hashtbl.find_opt Decls.ctor_owner (intern cname) with
        | None -> type_error ("未知のコンストラクタ: " ^ show_long_id li)
        | Some dname ->
            let ctor = intern cname in
            let dd = Hashtbl.find Decls.datas dname in
            if dd.Decls.dd_opaque then type_error ("newtype " ^ name_of dname ^ " の表現は ??? で隠されています")
            else
              let ct = List.find (fun c -> c.Decls.ct_name = ctor) dd.Decls.dd_ctors in
              let nfields = List.length ct.Decls.ct_fields in
              let field_to_arg = Array.make nfields None in
              let positional = List.filter (fun a -> a.T.cap_label = None) args in
              (* 位置引数があるときは全フィールドが必要。欠落の _ 補完はラベル指定パターンのみ(§2.1) *)
              if positional <> [] && List.length args <> nfields then
                type_error
                  (Printf.sprintf "コンストラクタ %s のパターンは %d 個のフィールドを取ります(%d 個与えられました)" cname nfields
                     (List.length args));
              List.iteri
                (fun ai (a : T.ctor_arg_pat) ->
                  match a.T.cap_label with
                  | None ->
                      let rec first i =
                        if i >= nfields then type_error ("コンストラクタ " ^ cname ^ " のパターンの引数が多すぎます")
                        else if field_to_arg.(i) = None then i
                        else first (i + 1)
                      in
                      field_to_arg.(first 0) <- Some ai
                  | Some l ->
                      let lo = intern l in
                      let rec find i = function
                        | [] -> type_error ("コンストラクタ " ^ cname ^ " にフィールド " ^ l ^ " はありません")
                        | f :: rest -> if f.Decls.fi_label = Some lo then i else find (i + 1) rest
                      in
                      let i = find 0 ct.Decls.ct_fields in
                      if field_to_arg.(i) <> None then type_error ("フィールド " ^ l ^ " が二重に指定されています");
                      field_to_arg.(i) <- Some ai)
                args;
              Tree.set_resolved node (Tree.RCtorPat (dname, ctor, field_to_arg));
              let subst =
                List.map (fun (i : var_info) -> (i.vid, new_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
              in
              Unify.unify expected (TCon (dname, List.map snd subst));
              let env = ref env in
              Array.iteri
                (fun fi arg ->
                  match arg with
                  | Some ai ->
                      let f = List.nth ct.Decls.ct_fields fi in
                      env := elab_pat !env level seen (Unify.subst_params level subst f.Decls.fi_ty) (List.nth args ai).T.cap_pat
                  | None -> ())
                field_to_arg;
              !env)

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
          | LongId comps when comps <> [] && String.length (List.nth comps (List.length comps - 1)) > 0 ->
              let last = List.nth comps (List.length comps - 1) in
              if last.[0] >= 'A' && last.[0] <= 'Z' then elab_construct env level node last []
              else type_error ("未束縛の変数: " ^ name)
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
      let tr = new_var level in
      let pvar = new_var level in
      (* 関数の行を呼び出し側の eff と単一化(MiniLang:1319-1324。既存バグ 0.2-4 の修正)。
         関数型を先に分解してから引数を期待型で検査する(引数のラムダの行が
         本体の perform 解決(D22)より先に確定するために必須) *)
      Unify.unify tf (TArrow (pvar, tr, eff));
      elab_check env level eff arg pvar;
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
  | T.Match (scrut, clauses) ->
      let tscrut = elab_exp env level eff scrut in
      let tres = new_var level in
      List.iter
        (fun ((_, c) : T.clause) ->
          let seen = ref [] in
          let env2 = elab_pat env level seen tscrut c.T.cl_pat in
          (match c.T.cl_guard with
          | Some g -> Unify.unify (elab_exp env2 level eff g) t_boolean
          | None -> ());
          Unify.unify (elab_exp env2 level eff c.T.cl_body) tres)
        clauses;
      Exhaust.queue (List.map (fun ((_, c) : T.clause) -> (c.T.cl_pat, c.T.cl_guard <> None)) clauses) tscrut;
      tres
  | T.Construct (li, args) ->
      let (LongId comps) = li in
      elab_construct env level node
        (List.nth comps (List.length comps - 1))
        ~eff
        (List.map (fun (a : T.ctor_arg) -> (a.T.ca_label, a.T.ca_exp)) args)
  | T.Perform (li, arg) ->
      let eff_name, op, scheme = resolve_perform env eff li in
      Tree.set_resolved node (Tree.ROp (intern (name_of eff_name ^ "." ^ name_of op)));
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      Unify.unify (elab_exp env level eff arg) args_row;
      (try Unify.unify eff (TRowExtend (eff_name, t_unit, new_row_var level))
       with Type_error msg -> type_error ("エフェクト " ^ name_of eff_name ^ " をここでは実行できません(" ^ msg ^ ")"));
      op_ret
  | T.Handle (body, clauses) -> elab_handle env level eff clauses body
  | T.Resume arg -> (
      match env.resume_ty with
      | None -> type_error "resume は操作節の中でのみ使えます"
      | Some (op_ret, tres) ->
          (match arg with
          | Some e -> Unify.unify (elab_exp env level eff e) op_ret
          | None ->
              (* 引数省略は操作の返り値型が Unit のときだけ(sample.kel:355) *)
              Unify.unify t_unit op_ret);
          tres)
  | T.Run (h, body) ->
      (* MiniLang:1530-1538。スコープに入る前に結果変数、level+1 で Rigid、本体を Heap[h] 行で推論 *)
      let result = new_var level in
      let heap = new_rigid (level + 1) in
      let env2 = { env with types = SMap.add h heap env.types } in
      let t = elab_exp env2 (level + 1) (TRowExtend (eff_heap, heap, eff)) body in
      Unify.unify result t;
      result

and elab_construct env level node cname ?eff args =
  let ctor = intern cname in
  match Hashtbl.find_opt Decls.ctor_owner ctor with
  | None -> type_error ("未知のコンストラクタ: " ^ cname)
  | Some dname ->
      let dd = Hashtbl.find Decls.datas dname in
      if dd.Decls.dd_opaque then type_error ("newtype " ^ name_of dname ^ " の表現は ??? で隠されています")
      else
        let ct = List.find (fun c -> c.Decls.ct_name = ctor) dd.Decls.dd_ctors in
        let nfields = List.length ct.Decls.ct_fields in
        let assigned = Array.make nfields false in
        let arg_to_field =
          Array.of_list
            (List.map
               (fun (label, _) ->
                 match label with
                 | None ->
                     let rec first i =
                       if i >= nfields then type_error ("コンストラクタ " ^ cname ^ " の引数が多すぎます")
                       else if assigned.(i) then first (i + 1)
                       else i
                     in
                     let i = first 0 in
                     assigned.(i) <- true;
                     i
                 | Some l ->
                     let lo = intern l in
                     let rec find i = function
                       | [] -> type_error ("コンストラクタ " ^ cname ^ " にフィールド " ^ l ^ " はありません")
                       | f :: rest -> if f.Decls.fi_label = Some lo then i else find (i + 1) rest
                     in
                     let i = find 0 ct.Decls.ct_fields in
                     if assigned.(i) then type_error ("フィールド " ^ l ^ " が二重に指定されています");
                     assigned.(i) <- true;
                     i)
               args)
        in
        if Array.exists not assigned then
          type_error ("コンストラクタ " ^ cname ^ " の引数が不足しています(式では全フィールド必須)");
        Tree.set_resolved node (Tree.RCtor (dname, ctor, arg_to_field));
        let subst =
          List.map (fun (i : var_info) -> (i.vid, new_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
        in
        List.iteri
          (fun ai (_, e) ->
            let f = List.nth ct.Decls.ct_fields arg_to_field.(ai) in
            let ety =
              match eff with
              | Some eff -> elab_exp env level eff e
              | None -> bug "elab_construct: 引数つきなのに eff がない"
            in
            Unify.unify ety (Unify.subst_params level subst f.Decls.fi_ty))
          args;
        TCon (dname, List.map snd subst)

(* 検査モード(軽い双方向化)。Lambda と引数レコードにだけ期待型を押し込み、
   それ以外は合成して単一化する。引数位置のラムダの行を本体 elaboration より
   先に確定させるのが目的(D22 の解決が行のラベルを見るため) *)
and elab_check env level eff ((_, e) as node : T.exp) expected =
  let fallback () = Unify.unify (elab_exp env level eff node) expected in
  match (e, repr expected) with
  | T.Lambda { l_params; l_body }, TArrow (pexp, rexp, eexp) -> (
      match repr pexp with
      | TRecord prow ->
          let fields, tail = row_fields prow in
          if
            repr tail = TRowEmpty
            && List.length fields = List.length l_params
            && List.for_all (fun (l, _) -> l = l_item) fields
          then (
            let seen = ref [] in
            let env2 = List.fold_left2 (fun env p (_, t) -> elab_pat env level seen t p) env l_params fields in
            Tree.set_ty node expected;
            elab_check env2 level eexp l_body rexp)
          else fallback ()
      | _ -> fallback ())
  | T.RecordExtend (rest, l, v), TRecord row -> (
      match Unify.rewrite_row row (intern l) with
      | fty, rest_row ->
          Tree.set_ty node expected;
          elab_check env level eff v fty;
          elab_check env level eff rest (TRecord rest_row)
      | exception Type_error _ -> fallback ())
  | _ -> fallback ()

(* D22: 操作名の解決。qualified なら宣言表を直接引く。非修飾で曖昧なら
   現在の eff 行に明示的に現れているエフェクトを優先し、それでも一意でなければ修飾を要求 *)
and resolve_perform env eff li =
  ignore env;
  match li with
  | LongId [ ename; op ] -> (
      let e = intern ename in
      match Decls.find_effect e with
      | None -> type_error ("未知のエフェクト: " ^ ename)
      | Some info -> (
          match List.assoc_opt (intern op) info.Decls.ef_ops with
          | Some scheme -> (e, intern op, scheme)
          | None -> type_error ("エフェクト " ^ ename ^ " に操作 " ^ op ^ " はありません")))
  | LongId [ op ] -> (
      let opo = intern op in
      match Decls.op_candidates opo with
      | [] -> type_error ("未知の操作: " ^ op)
      | [ e ] -> (e, opo, List.assoc opo (Option.get (Decls.find_effect e)).Decls.ef_ops)
      | many -> (
          (* 現在の eff 行に明示的に現れる候補のうち、最左(= 最内ハンドラ)を採る。
             Scoped Labels の最左一致と実行時の最内捕捉に一致する *)
          let labels = List.map fst (fst (row_fields eff)) in
          let pos e =
            let rec go i = function [] -> None | l :: tl -> if l = e then Some i else go (i + 1) tl in
            go 0 labels
          in
          let ranked = List.filter_map (fun e -> Option.map (fun i -> (i, e)) (pos e)) many in
          match List.sort compare ranked with
          | (_, e) :: _ -> (e, opo, List.assoc opo (Option.get (Decls.find_effect e)).Decls.ef_ops)
          | [] ->
              type_error
                ("操作 " ^ op ^ " は複数のエフェクト("
                ^ String.concat ", " (List.map name_of many)
                ^ ")に属します。" ^ name_of (List.hd many) ^ "." ^ op ^ " のように修飾してください")))
  | li -> type_error ("不正な操作名です: " ^ show_long_id li)

(* D19 の構文検査: 節本体を走査し、Lambda の内側の Resume をエラーにする。
   内側の Handle の本体はそのまま走査し、節には入らない(節は自分の検査を受ける) *)
and check_resume_static ?(in_lambda = false) ((_, e) : T.exp) =
  let go = check_resume_static ~in_lambda in
  match e with
  | T.Resume arg ->
      if in_lambda then type_error "resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)"
      else Option.iter go arg
  | T.Lambda { l_body; _ } -> check_resume_static ~in_lambda:true l_body
  | T.Handle (b, _) -> go b
  | T.Bool _ | T.Number _ | T.Text _ | T.Ident _ | T.Hole | T.RecordEmpty -> ()
  | T.Apply (f, a) ->
      go f;
      go a
  | T.Construct (_, args) -> List.iter (fun (a : T.ctor_arg) -> go a.T.ca_exp) args
  | T.Variant (_, v) -> go v
  | T.BinOp (l, _, r) ->
      go l;
      go r
  | T.Not v -> go v
  | T.Let ((_, b), rest) ->
      go b.T.lb_body;
      go rest
  | T.LetRec (bs, rest) ->
      List.iter (fun ((_, b) : T.let_binding) -> go b.T.lb_body) bs;
      go rest
  | T.Seq es -> List.iter go es
  | T.Match (scrut, cs) ->
      go scrut;
      List.iter
        (fun ((_, c) : T.clause) ->
          Option.iter go c.T.cl_guard;
          go c.T.cl_body)
        cs
  | T.RecordExtend (r, _, v) | T.RecordUpdate (r, _, v) ->
      go r;
      go v
  | T.RecordRestriction (r, _) | T.RecordSelection (r, _) -> go r
  | T.Perform (_, a) -> go a
  | T.Run (_, b) -> go b

(* handle(§7.3)。節の分類は頭の PCtor 名で行い resolved へ書く *)
and elab_handle env level eff clauses body =
  let classify ((_, c) as cnode : T.clause) =
    match snd c.T.cl_pat with
    | T.PVar "cancel" -> `Cancel cnode
    | T.PCtor (LongId comps, args) -> (
        match List.rev comps with
        | "cancel" :: _ ->
            if args <> [] then type_error "cancel(reason) は将来拡張です(v0 では case cancel のみ)" else `Cancel cnode
        | "return" :: _ -> (
            match args with
            | [ { T.cap_label = None; cap_pat } ] -> `Return (cap_pat, cnode)
            | _ -> type_error "return 節は case return(x) の形で書いてください")
        | op :: quals when op <> "" && op.[0] >= 'a' && op.[0] <= 'z' ->
            `Op (intern op, (match quals with [] -> None | _ -> Some (intern (String.concat "." (List.rev quals)))), args, cnode)
        | _ -> type_error ("handle の節は操作名 / return / cancel で始めてください: " ^ show_long_id (LongId comps)))
    | _ -> type_error "handle の節は操作名 / return / cancel で始めてください"
  in
  let classified = List.map classify clauses in
  let ops = List.filter_map (function `Op (op, q, args, cnode) -> Some (op, q, args, cnode) | _ -> None) classified in
  let rets = List.filter_map (function `Return (p, cnode) -> Some (p, cnode) | _ -> None) classified in
  let cancels = List.filter_map (function `Cancel cnode -> Some cnode | _ -> None) classified in
  (if List.length rets > 1 then type_error "return 節は1つまでです");
  (if List.length cancels > 1 then type_error "cancel 節は1つまでです");
  (if ops = [] then type_error "handle には少なくとも1つの操作節が必要です");
  (* D22: 対象エフェクトは「全節が属し全操作が網羅される」候補が一意であること *)
  let quals = List.filter_map (fun (_, q, _, _) -> q) ops in
  let op_names = List.map (fun (op, _, _, _) -> op) ops in
  let target =
    match List.sort_uniq compare quals with
    | [ e ] -> e
    | _ :: _ -> type_error "handle の節の修飾エフェクトが一致しません"
    | [] -> (
        let declares e op = List.mem_assoc op (Option.get (Decls.find_effect e)).Decls.ef_ops in
        let all_effects = List.sort_uniq compare (List.concat_map Decls.op_candidates op_names) in
        let holds_all = List.filter (fun e -> List.for_all (declares e) op_names) all_effects in
        let covered =
          List.filter
            (fun e -> List.for_all (fun (op, _) -> List.mem op op_names) (Option.get (Decls.find_effect e)).Decls.ef_ops)
            holds_all
        in
        match covered with
        | [ e ] -> e
        | [] -> (
            match holds_all with
            | e :: _ ->
                let missing =
                  List.filter
                    (fun (op, _) -> not (List.mem op op_names))
                    (Option.get (Decls.find_effect e)).Decls.ef_ops
                in
                type_error
                  ("ハンドラが操作を網羅していません: " ^ name_of e ^ " の "
                  ^ String.concat ", " (List.map (fun (op, _) -> name_of op) missing)
                  ^ " が漏れています")
            | [] -> type_error ("この操作の組を宣言するエフェクトがありません: " ^ String.concat ", " (List.map name_of op_names)))
        | es ->
            type_error
              ("handle の対象エフェクトが曖昧です(" ^ String.concat ", " (List.map name_of es)
             ^ ")。" ^ name_of (List.hd es) ^ "." ^ name_of (List.hd op_names) ^ " のように修飾してください"))
  in
  let target_info = Option.get (Decls.find_effect target) in
  (* 対象確定後の検査: 全操作の網羅と、全節の所属 *)
  List.iter
    (fun (op, _) ->
      if not (List.mem op op_names) then
        type_error ("ハンドラが操作を網羅していません: " ^ name_of target ^ " の " ^ name_of op ^ " が漏れています"))
    target_info.Decls.ef_ops;
  List.iter
    (fun (op, _, _, _) ->
      if not (List.mem_assoc op target_info.Decls.ef_ops) then
        type_error ("操作 " ^ name_of op ^ " はエフェクト " ^ name_of target ^ " に属しません"))
    ops;
  (* 本体は対象エフェクトを積んだ行で推論 *)
  let body_ty = elab_exp env level (TRowExtend (target, t_unit, eff)) body in
  let tres = new_var level in
  (* return 節・cancel 節は外側の eff で推論(retc/exnc は自分のハンドラが外れた文脈で走る、§7.3) *)
  (match rets with
  | [ (p, ((_, c) as cnode)) ] ->
      Tree.set_resolved cnode Tree.RReturnClause;
      let seen = ref [] in
      let env2 = elab_pat { env with resume_ty = None } level seen body_ty p in
      (match c.T.cl_guard with Some g -> Unify.unify (elab_exp env2 level eff g) t_boolean | None -> ());
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres
  | _ -> Unify.unify body_ty tres);
  (match cancels with
  | [ ((_, c) as cnode) ] ->
      Tree.set_resolved cnode Tree.RCancelClause;
      let env2 = { env with resume_ty = None } in
      (match c.T.cl_guard with Some g -> Unify.unify (elab_exp env2 level eff g) t_boolean | None -> ());
      (* cancel 節の値は捨てられる: Unit と単一化(§7.3) *)
      Unify.unify (elab_exp env2 level eff c.T.cl_body) t_unit
  | _ -> ());
  (* 操作節 *)
  List.iter
    (fun (op, _, args, ((_, c) as cnode)) ->
      Tree.set_resolved cnode (Tree.ROp (intern (name_of target ^ "." ^ name_of op)));
      let scheme = List.assoc op target_info.Decls.ef_ops in
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      let param_tys = match repr args_row with TRecord row -> List.map snd (fst (row_fields row)) | _ -> [] in
      if List.length args <> List.length param_tys then
        type_error
          (Printf.sprintf "操作 %s は %d 引数です(節には %d 個書かれています)" (name_of op) (List.length param_tys)
             (List.length args));
      List.iter (fun (a : T.ctor_arg_pat) -> if a.T.cap_label <> None then type_error "操作節の引数にラベルは書けません") args;
      let seen = ref [] in
      let env2 =
        List.fold_left2
          (fun env (a : T.ctor_arg_pat) t -> elab_pat env level seen t a.T.cap_pat)
          env args param_tys
      in
      (* 操作節では resume が使える。本体は外側の eff で推論(MiniLang:1499) *)
      let env2 = { env2 with resume_ty = Some (op_ret, tres) } in
      check_resume_static c.T.cl_body;
      (match c.T.cl_guard with Some g -> Unify.unify (elab_exp env2 level eff g) t_boolean | None -> ());
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres)
    ops;
  tres

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

(* 明示的なラベル付き閉行の eff 注釈(@ Print / @ {A, B})は、本体検査では Rigid 尾部、
   公開スキーマでは Generic 尾部として開く(sample.kel:357 の handle がこれを要求する。
   Rigid 尾部なので本体が注釈に無いエフェクトを起こすことは引き続き拒否される)。
   @ {}(ラベルなし閉行)は閉じたまま = 純粋。裁定の経緯は doc/log を参照 *)
and open_explicit_eff lvl eff =
  let fields, tail = row_fields eff in
  match repr tail with
  | TRowEmpty when fields <> [] ->
      let r = ref (Rigid { vid = new_oid (); vlevel = lvl; vkind = KRow; vcls = [] }) in
      (row_append eff (TVar r), [ ("", TVar r, r) ])
  | _ -> (eff, [])

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
  let extra_rigids = ref [] in
  let rigids = make_rigids lvl b.T.lb_tparams in
  let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
  let fn_ty =
    match b.T.lb_params with
    | Some params ->
        let seen = ref [] in
        let param_tys = List.map (fun _ -> new_var lvl) params in
        let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
        let fn_eff, eff_rigids =
          match b.T.lb_eff with Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e) | None -> (new_row_var lvl, [])
        in
        extra_rigids := eff_rigids @ !extra_rigids;
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
  let rigids = rigids @ !extra_rigids in
  (* 網羅性の遅延キューは generalize の直前に drain する(§7.2) *)
  match snd b.T.lb_name with
  | T.PVar x ->
      List.iter warn (Exhaust.drain ());
      if gen then Unify.generalize level fn_ty;
      release_rigids rigids;
      { env with values = SMap.add x fn_ty env.values }
  | T.PWildcard ->
      List.iter warn (Exhaust.drain ());
      if gen then Unify.generalize level fn_ty;
      release_rigids rigids;
      env
  | _ ->
      (* パターン束縛は単相(単一ケース match と同じ扱い、§6.4)。網羅性警告に乗せる *)
      release_rigids rigids;
      let seen = ref [] in
      let env' = elab_pat env level seen fn_ty b.T.lb_name in
      Exhaust.queue [ (b.T.lb_name, false) ] fn_ty;
      List.iter warn (Exhaust.drain ());
      env'

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
      let extra_rigids = ref [] in
      let fn_ty =
        match b.T.lb_params with
        | Some params ->
            let seen = ref [] in
            let param_tys = List.map (fun _ -> new_var lvl) params in
            let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
            let fn_eff, eff_rigids =
              match b.T.lb_eff with
              | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
              | None -> (new_row_var lvl, [])
            in
            extra_rigids := eff_rigids;
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
      release_rigids (rigids @ !extra_rigids))
    bs names;
  List.iter warn (Exhaust.drain ());
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

(* newtype 宣言の登録(パス1)。フィールド型のパラメータは Generic 変数で束縛して
   スキーマとして表に置く(組み込みメソッドスキーマと同じ形、§7.3) *)
let register_newtype env (n : T.newtype') =
  let params =
    List.map
      (fun tp ->
        (* newtype パラメータのカインドは * か、F[_] 明示のみ(v0) *)
        let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else KStar in
        let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
        { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes })
      n.T.nt_params
  in
  let types =
    List.fold_left2
      (fun m (tp : type_param) i -> SMap.add tp.tp_name (TVar (ref (Generic i))) m)
      env.types n.T.nt_params params
  in
  let env' = { env with types } in
  match n.T.nt_rhs with
  | T.NtHole ->
      Decls.add_data { Decls.dd_name = intern n.T.nt_name; dd_params = params; dd_ctors = []; dd_opaque = true }
  | T.NtCtors ctors ->
      let ctors =
        List.map
          (fun (c : T.ctor_decl) ->
            {
              Decls.ct_name = intern c.T.cd_name;
              ct_fields =
                List.map
                  (fun (f : T.field_decl) ->
                    let ty = elab_type env' 1 f.T.fd_ty in
                    (* 省略された @ など、束縛されなかった変数はスキーマでは Generic にする *)
                    Unify.generalize 0 ty;
                    { Decls.fi_label = Option.map intern f.T.fd_label; fi_ty = ty })
                  c.T.cd_fields;
            })
          ctors
      in
      Decls.add_data { Decls.dd_name = intern n.T.nt_name; dd_params = params; dd_ctors = ctors; dd_opaque = false }

(* effect 宣言の登録(パス1、§7.3)。操作の型は矢印スキーマで表に置く *)
let register_effect env (e : T.effect') =
  if e.T.ef_params <> [] then type_error "effect 宣言に型パラメータは書けません(sample.kel §9)";
  let ops =
    List.map
      (fun (op, te) ->
        match snd te with
        | T.EArrow _ ->
            let ty = elab_type env 1 te in
            Unify.generalize 0 ty;
            (intern op, ty)
        | _ -> type_error ("操作 " ^ op ^ " の型は矢印型でなければなりません"))
      e.T.ef_ops
  in
  (* 同一 effect 内の重複 op は拒否 *)
  let rec dup = function
    | [] -> ()
    | (op, _) :: rest -> if List.mem_assoc op rest then type_error ("操作 " ^ name_of op ^ " が二重に宣言されています") else dup rest
  in
  dup ops;
  Decls.add_effect { Decls.ef_name = intern e.T.ef_name; ef_ops = ops }

let binding_name (b : T.let_binding') = match snd b.T.lb_name with T.PVar x -> Some x | _ -> None

(* type class 宣言の登録(パス1、§7.4)。1パラメータのみ(D11)。
   メソッドはクラスパラメータ(vcls つき Generic)とメソッド固有型パラメータの
   両方を Generic 化したスキーマとして表に置く *)
let register_class env (c : T.class_decl') =
  let cls = intern c.T.cls_name in
  (if c.T.cls_name = "Integral" || c.T.cls_name = "Fractional" then
     type_error (c.T.cls_name ^ " は予約されたリテラル述語です(ユーザ宣言不可、D8)"));
  let param =
    match c.T.cls_params with
    | [ p ] -> p
    | _ -> type_error "type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:275)"
  in
  let param_kind = if param.tp_arity > 0 then k_arrow param.tp_arity else KStar in
  (if param.tp_classes <> [] then type_error "クラスパラメータに制約は書けません(スーパークラスは v1)");
  let pinfo = { vid = new_oid (); vlevel = 0; vkind = param_kind; vcls = [ cls ] } in
  let pvar = TVar (ref (Generic pinfo)) in
  List.iter
    (fun d -> if d <> "structural" then type_error ("未知の導出規則: " ^ d ^ "(v0 は derive structural のみ)"))
    c.T.cls_derives;
  let methods =
    List.map
      (fun (v : T.class_val) ->
        let mt_params =
          List.map
            (fun tp ->
              (* カインドは使用位置から推論し、宣言終了時に KStar へ既定化(D7) *)
              let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
              let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
              (tp.tp_name, TVar (ref (Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))))
            v.T.cv_tparams
        in
        let types = List.fold_left (fun m (n, t) -> SMap.add n t m) (SMap.add param.tp_name pvar env.types) mt_params in
        let ty = elab_type { env with types } 1 v.T.cv_ty in
        Unify.generalize 0 ty;
        List.iter (fun (_, t) -> match repr t with TVar r -> default_kind (Unify.var_info_of r).vkind | _ -> ()) mt_params;
        (* v0 制約: クラスパラメータが少なくとも1つの引数位置に現れること(§7.4。実行時ディスパッチの前提) *)
        let rec occurs t =
          match repr t with
          | TVar r -> ( match !r with Generic i -> i.vid = pinfo.vid | _ -> false)
          | TCon (_, args) -> List.exists occurs args
          | TApp (f, a) -> occurs f || occurs a
          | TArrow (p, r, e) -> occurs p || occurs r || occurs e
          | TRecord row | TVariant row -> occurs row
          | TRowEmpty -> false
          | TRowExtend (_, f, rest) -> occurs f || occurs rest
        in
        (match repr ty with
        | TArrow (args, _, _) when occurs args -> ()
        | TArrow _ ->
            type_error
              ("メソッド " ^ v.T.cv_name ^ " はクラスパラメータが引数位置に現れないため v0 では宣言できません(実行時ディスパッチの前提、§7.4)")
        | _ -> type_error ("メソッド " ^ v.T.cv_name ^ " の型は矢印型でなければなりません"));
        (v.T.cv_name, ty))
      c.T.cls_vals
  in
  match
    Decls.add_class_decl
      {
        Decls.ci_name = cls;
        ci_param = pinfo;
        ci_param_kind = param_kind;
        ci_derive_structural = List.mem "structural" c.T.cls_derives;
        ci_builtin = false;
        ci_methods = methods;
      }
  with
  | `Added -> methods
  | `Builtin prev ->
      (* 組み込みと同名: メソッド名の集合が一致することだけ照合し、実体は組み込みを使う *)
      List.iter
        (fun (m, _) ->
          if not (List.mem_assoc m prev.Decls.ci_methods) then
            type_error ("組み込みクラス " ^ c.T.cls_name ^ " に無いメソッド " ^ m ^ " は宣言できません"))
        methods;
      prev.Decls.ci_methods

(* type instance 宣言の頭の登録(パス1、§7.4)。頭は 構成子[_..] の形 *)
let instance_head (i : T.instance_decl') =
  let cls = intern i.T.ins_class in
  let head =
    match i.T.ins_args with
    | [ h ] -> h
    | _ -> type_error "type instance の型引数は1個です(D11)"
  in
  let con, holes =
    match snd head with
    | T.EIdent (LongId [ n ]) -> (intern n, 0)
    | T.EApply ((_, T.EIdent (LongId [ n ])), args) ->
        List.iter (fun (a : T.type_exp) -> match snd a with T.EHole -> () | _ -> type_error "インスタンス頭の型引数は _ だけです(List[_] の形)") args;
        (intern n, List.length args)
    | _ -> type_error "インスタンス頭は 型構成子 か 型構成子[_, ...] の形で書いてください"
  in
  (cls, con, holes)

let register_instance (i : T.instance_decl') =
  let cls, con, holes = instance_head i in
  let ci = match Decls.find_class cls with Some ci -> ci | None -> type_error ("未知のクラス: " ^ i.T.ins_class) in
  if not (Hashtbl.mem Decls.con_kinds con) then type_error ("未知の型構成子: " ^ name_of con);
  if not (same_kind ci.Decls.ci_param_kind (Decls.con_kind con holes)) then
    type_error
      ("インスタンス頭 " ^ name_of con ^ " のカインドがクラス " ^ i.T.ins_class ^ " のパラメータと一致しません");
  let methods =
    List.concat_map
      (fun ((_, d) : T.decl) ->
        let name_of_b ((_, b) as bnode : T.let_binding) =
          match binding_name b with
          | Some x -> (intern x, bnode)
          | None -> type_error "インスタンス本体の let は名前束縛でなければなりません"
        in
        match d with
        | T.DLet bnode -> [ name_of_b bnode ]
        | T.DLetRec bs -> List.map name_of_b bs
        | _ -> type_error "インスタンス本体には let(と let rec)だけが書けます")
      i.T.ins_body
  in
  (* メソッドの網羅と過剰 *)
  List.iter
    (fun (m, _) ->
      if not (List.exists (fun (m2, _) -> intern m2 = m) ci.Decls.ci_methods) then
        type_error ("クラス " ^ i.T.ins_class ^ " にメソッド " ^ name_of m ^ " はありません"))
    methods;
  List.iter
    (fun (m, _) ->
      if not (List.mem_assoc (intern m) methods) then
        type_error ("インスタンスがメソッドを網羅していません: " ^ m ^ " が漏れています"))
    ci.Decls.ci_methods;
  Decls.add_instance ~builtin:false ~methods ~cls ~con []

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
            let fn_eff, eff_rigids =
              match b.T.lb_eff with
              | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
              | None -> (new_row_var lvl, [])
            in
            let ret_ty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> assert false in
            release_rigids eff_rigids;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None -> ( match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> assert false)
      in
      Unify.generalize 0 ty;
      release_rigids rigids;
      Some ty
    with Type_error _ | NotImplemented _ -> None

(* インスタンスメソッド本体の検査(パス2、§7.4)。
   本体を通常どおり推論・一般化してから、「クラス宣言のメソッド型に頭型を代入した型」への
   包摂(instantiate した推論型 = skolemize した期待型)を検査する。
   let rec と注釈付きメソッド(sample.kel:321-324 の Functor[List[_]])もこの経路で通る *)
let check_instance_bodies env (i : T.instance_decl') =
  let cls, con, _holes = instance_head i in
  let ci = match Decls.find_class cls with Some ci -> ci | None -> bug "instance: class 未登録" in
  let head_ty = TCon (con, []) in
  let expected_of mname =
    match List.assoc_opt mname ci.Decls.ci_methods with
    | Some scheme ->
        let memo = Hashtbl.create 8 in
        Hashtbl.add memo ci.Decls.ci_param.vid head_ty;
        Unify.map_generics_with memo (fun info -> TVar (ref (Generic info))) scheme
    | None -> bug "instance: メソッドスキーマ未登録"
  in
  let subsume mname inferred =
    let lvl = 1 in
    let skol = Unify.skolemize lvl (expected_of mname) in
    try Unify.unify (Unify.instantiate lvl inferred) skol
    with Type_error msg ->
      type_error ("インスタンスメソッド " ^ mname ^ " がクラス宣言の型を満たしません(" ^ msg ^ ")")
  in
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet ((_, b) as bnode) ->
          let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
          let env2 = elab_binding env 0 (new_row_var 0) bnode in
          subsume mname (SMap.find mname env2.values)
      | T.DLetRec bs ->
          let env2 = elab_rec_bindings env 0 (new_row_var 0) bs in
          List.iter
            (fun ((_, b) : T.let_binding) ->
              let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
              subsume mname (SMap.find mname env2.values))
            bs
      | _ -> type_error "インスタンス本体には let だけが書けます")
    i.T.ins_body

(* 宣言列の型検査。出力行(name : type / ⚠)を返す。型エラーは最初の1つで Type_error *)
let type_check_decls decls =
  warnings := [];
  Unify.reset ();
  Exhaust.reset ();
  let out = current_out in
  out := [];
  let emit s = out := !out @ [ s ] in
  let eff0 = toplevel_eff () in
  let env0 = initial_env () in
  (* パス1a: 型エイリアスの登録と newtype の頭(カインド)。§7.2 *)
  List.iter
    (fun (_, d) ->
      match d with
      | T.DType t ->
          Decls.add_alias
            { Decls.al_name = intern t.T.ta_name; al_params = t.T.ta_params; al_kind = t.T.ta_kind; al_body = t.T.ta_body }
      | T.DNewtype n -> Hashtbl.replace Decls.con_kinds (intern n.T.nt_name) (k_arrow (List.length n.T.nt_params))
      | _ -> ())
    decls;
  (* パス1b: newtype のコンストラクタ・effect・type class の登録(相互再帰・前方参照可) *)
  let env0 =
    List.fold_left
      (fun env (_, d) ->
        match d with
        | T.DNewtype n ->
            register_newtype env n;
            env
        | T.DEffect e ->
            register_effect env e;
            env
        | T.DClass c ->
            let methods = register_class env c in
            (* メソッドを非修飾名と修飾名の両方で値環境に登録(§7.4) *)
            {
              env with
              values =
                List.fold_left
                  (fun m (mn, ty) -> SMap.add mn ty (SMap.add (c.T.cls_name ^ "." ^ mn) ty m))
                  env.values methods;
            }
        | _ -> env)
      env0 decls
  in
  (* パス1c: インスタンス頭の登録と、注釈が完全な let の署名登録 *)
  let env =
    List.fold_left
      (fun env (_, d) ->
        match d with
        | T.DInstance i ->
            register_instance i;
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
          List.iter warn (Exhaust.drain ());
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
          let fn_eff, eff_rigids =
            match ex.T.ex_eff with Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e) | None -> (new_row_var lvl, [])
          in
          let ret_ty = match ex.T.ex_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
          let ty = TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff) in
          Unify.generalize 0 ty;
          release_rigids (rigids @ eff_rigids);
          emit (ex.T.ex_name ^ " : " ^ Show.show ty);
          { env with values = SMap.add ex.T.ex_name ty env.values }
      | T.DNewtype _ -> env (* パス1で登録済み。フィールド型の検査も登録時に済んでいる *)
      | T.DEffect _ -> env (* パス1で登録済み *)
      | T.DClass _ -> env (* パス1で登録済み *)
      | T.DInstance i ->
          check_instance_bodies env i;
          env
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

(* 返り値: (エラーまでに得られた出力行, エラー行 option)。
   型エラーは最初の1つで打ち切る(§9.2)が、そこまでの結果は出力する *)
let type_check decls =
  current_out := [];
  try (type_check_decls decls, None) with
  | Type_error msg -> (!current_out, Some ("! 型エラー: " ^ msg))
  | Syntax_error msg -> (!current_out, Some ("! 構文エラー: " ^ msg))
