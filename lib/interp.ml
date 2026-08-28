(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 評価器本体(計画 §8.3-§8.5)。
 *
 * 末尾呼び出し規約(§8.3): eval の末尾位置(Apply のクロージャ本体、Match / ブロックの
 * 本体)を OCaml の末尾呼び出しに保つ。eval の再帰を try...with で包まない(1枚で TCO が
 * 消える)。エラー装飾は driver の最外周1回だけ。
 * 評価順序「左から右」は OCaml の未規定評価順に任せず let で固定する。
 *)
open Aux
open Syntax
open Value
module T = Tree.Tree

(* ユーザ宣言インスタンスのメソッド実体: (クラス, 型構成子) → メソッド名 → 値 *)
let user_instances : (oid * oid, (oid * Value.t) list) Hashtbl.t = Hashtbl.create 32

let tycon_of_value = function
  | VBool _ -> Some (Type.intern "Boolean")
  | VInt32 _ -> Some (Type.intern "Int32")
  | VInt64 _ -> Some (Type.intern "Int64")
  | VFloat64 _ -> Some (Type.intern "Float64")
  | VText _ -> Some (Type.intern "String")
  | VData d -> Some d.d_type
  | VRef _ -> Some (Type.intern "Ref")
  | VArray _ -> Some (Type.intern "Array")
  | VRecord _ | VVariant _ | VClosure _ | VPrim _ -> None

(* cancel 節内の例外の抑制ログ(sample.kel:392)。driver が差し替える *)
let cancel_log : (string -> unit) ref = ref (fun _ -> ())

(* ---- パターン照合 ---- *)

let rec match_pat locals ((_, p) as node : T.pat) v =
  match p with
  | T.PWildcard -> Some locals
  | T.PVar x -> Some (SMap.add x v locals)
  | T.PAnnot (sub, _) -> match_pat locals sub v
  | T.PBool b -> ( match v with VBool b2 when b = b2 -> Some locals | _ -> None)
  | T.PText s -> ( match v with VText s2 when String.equal s s2 -> Some locals | _ -> None)
  | T.PNumber n -> (
      match v with
      | VInt32 x -> ( match Int32.of_string_opt n.n_text with Some y when x = y -> Some locals | _ -> None)
      | VInt64 x -> ( match Int64.of_string_opt n.n_text with Some y when x = y -> Some locals | _ -> None)
      | VFloat64 x -> ( match float_of_string_opt n.n_text with Some y when x = y -> Some locals | _ -> None)
      | _ -> None)
  | T.PVariant (s, sub) -> (
      match v with VVariant (l, payload) when l = Type.intern s -> match_pat locals sub payload | _ -> None)
  | T.PRecord (fields, rest) -> (
      let rec go locals remaining = function
        | [] -> (
            match rest with None -> Some locals | Some rp -> match_pat locals rp remaining)
        | (l, sub) :: tl -> (
            match record_take remaining (Type.intern l) with
            | x, remaining' -> ( match match_pat locals sub x with Some locals -> go locals remaining' tl | None -> None)
            | exception Runtime_error _ -> None)
      in
      match v with VRecord _ -> go locals v fields | _ -> None)
  | T.PCtor (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtorPat (_, ctor, field_to_arg)) -> (
          match v with
          | VData d when d.d_ctor = ctor ->
              let rec go locals fi =
                if fi >= Array.length field_to_arg then Some locals
                else
                  match field_to_arg.(fi) with
                  | None -> go locals (fi + 1)
                  | Some ai -> (
                      match match_pat locals (List.nth args ai).T.cap_pat d.d_fields.(fi) with
                      | Some locals -> go locals (fi + 1)
                      | None -> None)
              in
              go locals 0
          | _ -> None)
      | _ -> bug "PCtor が解決されていません")

let bind_pat_exn locals pat v =
  match match_pat locals pat v with
  | Some locals -> locals
  | None -> runtime_error ("パターンに値が一致しません: " ^ show v)

(* ---- 評価器 ---- *)

let number_value node (n : number) =
  let head =
    match Type.repr (Tree.get_ty node) with
    | Type.TCon (c, _) -> Type.name_of c
    | _ -> runtime_error "数値リテラルの型が解決されていません"
  in
  try
    match head with
    | "Int32" -> VInt32 (Int32.of_string n.n_text)
    | "Int64" -> VInt64 (Int64.of_string n.n_text)
    | "Float64" -> VFloat64 (float_of_string n.n_text)
    | t -> runtime_error ("数値リテラルの型が不正です: " ^ t)
  with Failure _ -> runtime_error ("数値リテラルが範囲外です: " ^ Lexer.show_number n)

let rec eval env ((_, e) as node : T.exp) : Value.t =
  match e with
  | T.Bool b -> VBool b
  | T.Text s -> VText s
  | T.Number n -> number_value node n (* 唯一 elab の型を読む場所(§8.3) *)
  | T.Hole -> runtime_error "??? に到達しました"
  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.locals with
      | Some v -> v
      | None -> (
          match Hashtbl.find_opt env.globals name with
          | Some v -> v
          | None -> (
              (* 裸の引数なしコンストラクタ *)
              match Tree.get_resolved node with
              | Some (Tree.RCtor (d, c, _)) -> VData { d_type = d; d_ctor = c; d_fields = [||] }
              | _ -> runtime_error ("未束縛の変数: " ^ name))))
  | T.Lambda { l_params; l_body } -> VClosure { c_env = env; c_params = l_params; c_body = l_body }
  | T.Apply (f, arg) ->
      let vf = eval env f in
      let va = eval env arg in
      apply vf va
  | T.Construct (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtor (d, c, arg_to_field)) ->
          let fields = Array.make (Array.length arg_to_field) unit in
          List.iteri
            (fun ai (a : T.ctor_arg) ->
              (* 評価はソース順、格納は宣言フィールド順(resolved の対応表) *)
              fields.(arg_to_field.(ai)) <- eval env a.T.ca_exp)
            args;
          VData { d_type = d; d_ctor = c; d_fields = fields }
      | _ -> bug "Construct が解決されていません")
  | T.Variant (s, payload) -> VVariant (Type.intern s, eval env payload)
  | T.BinOp (l, op, r) -> (
      match Prims.bin_op_sem op with
      | Prims.OpBool -> (
          (* 短絡(sample.kel:283) *)
          match op with
          | And -> if Builtin.as_bool (eval env l) then eval env r else VBool false
          | Or -> if Builtin.as_bool (eval env l) then VBool true else eval env r
          | _ -> bug "OpBool")
      | Prims.OpMethod (cls, m) ->
          let vl = eval env l in
          let vr = eval env r in
          dispatch cls m (VRecord [ (Type.l_item, vl); (Type.l_item, vr) ])
      | Prims.OpMethodNot (cls, m) ->
          let vl = eval env l in
          let vr = eval env r in
          VBool (not (Builtin.as_bool (dispatch cls m (VRecord [ (Type.l_item, vl); (Type.l_item, vr) ])))))
  | T.Not e -> VBool (not (Builtin.as_bool (eval env e)))
  | T.Let (b, rest) ->
      let locals = eval_binding env b in
      eval { env with locals } rest
  | T.LetRec (bs, rest) ->
      let locals = eval_rec_bindings env bs in
      eval { env with locals } rest
  | T.Seq es ->
      let rec go = function
        | [] -> unit
        | [ last ] -> eval env last
        | s :: rest ->
            let _ = eval env s in
            go rest
      in
      go es
  | T.Match (scrut, clauses) ->
      let v = eval env scrut in
      let rec try_clauses = function
        | [] -> runtime_error ("match のどの節にも一致しません: " ^ show v)
        | ((_, c) : T.clause) :: rest -> (
            match match_pat env.locals c.T.cl_pat v with
            | None -> try_clauses rest
            | Some locals -> (
                let env2 = { env with locals } in
                match c.T.cl_guard with
                | Some g -> if Builtin.as_bool (eval env2 g) then eval env2 c.T.cl_body else try_clauses rest
                | None -> eval env2 c.T.cl_body))
      in
      try_clauses clauses
  | T.RecordEmpty -> unit
  | T.RecordExtend (rest, l, v) ->
      (* value が先、rest が後(sample.kel:203。AST のフィールド順と逆、§8.3) *)
      let vv = eval env v in
      let vrest = eval env rest in
      record_extend vrest (Type.intern l) vv
  | T.RecordUpdate (r, l, v) ->
      let vr = eval env r in
      let vv = eval env v in
      record_update vr (Type.intern l) vv
  | T.RecordRestriction (r, l) -> record_restrict (eval env r) (Type.intern l)
  | T.RecordSelection (r, l) -> record_select (eval env r) (Type.intern l)
  | T.Perform (_, arg) -> (
      match Tree.get_resolved node with
      | Some (Tree.ROp op) ->
          let va = eval env arg in
          Effect.perform (Op (op, va))
      | _ -> bug "Perform が解決されていません")
  | T.Handle (body, clauses) -> eval_handle env body clauses
  | T.Resume arg -> (
      match env.resume with
      | None -> runtime_error "resume は操作節の中でのみ使えます"
      | Some r ->
          (* 引数を先に評価する: resume(f()) の f が例外で脱出したら resume は未消費のまま
             節の例外経路(discontinue)に乗る *)
          let v = match arg with Some e -> eval env e | None -> unit in
          if not r.r_alive then runtime_error "resume を節の外で呼び出しました(second-class)"
          else if r.r_used then runtime_error "resume は高々1回しか呼べません(アフィン)"
          else (
            r.r_used <- true;
            Effect.Deep.continue r.r_k v))
  | T.Run (_, body) -> eval env body (* 実行時は恒等。型が安全性を保証する(§8.4) *)

and apply vf vargs =
  match vf with
  | VClosure c ->
      let fields = record_fields vargs in
      if List.length fields <> List.length c.c_params then
        runtime_error
          (Printf.sprintf "引数の個数が一致しません(%d 引数の関数に %d 個)" (List.length c.c_params) (List.length fields))
      else
        let locals =
          List.fold_left2 (fun locals p (_, v) -> bind_pat_exn locals p v) c.c_env.locals c.c_params fields
        in
        eval { c.c_env with locals } c.c_body
  | VPrim p -> p.p_fn vargs
  | v -> runtime_error ("関数ではない値を適用しました: " ^ show v)

(* ---- 型クラスの実行時ディスパッチ(D3、§8.5) ---- *)

(* メソッドスキーマから「クラスパラメータが頭に現れる引数位置」を求める。
   ここだけでディスパッチする(elab.ml の register_class と同じ規約)。
   これを守らないと pick: (Int32, A) => Int32 が第1引数の Int32 で
   誤ってディスパッチし、elab の解決と食い違う(検証で実証) *)
and dispatch_positions ci meth =
  let is_param t =
    match Type.repr (fst (Type.app_spine t)) with
    | Type.TVar r -> ( match !r with Type.Generic i -> i.Type.vid = ci.Decls.ci_param.Type.vid | _ -> false)
    | _ -> false
  in
  match List.assoc_opt meth ci.Decls.ci_methods with
  | Some scheme -> (
      match Type.repr scheme with
      | Type.TArrow (args, _, _) -> (
          match Type.repr args with
          | Type.TRecord row ->
              fst (Type.row_fields row)
              |> List.mapi (fun i (_, t) -> (i, t))
              |> List.filter_map (fun (i, t) -> if is_param t then Some i else None)
          | _ -> [])
      | _ -> [])
  | None -> []

and dispatch cls_name meth args =
  let cls_oid = Type.intern cls_name in
  let vals = Builtin.arg_values args in
  let cand_vals =
    match Decls.find_class cls_oid with
    | Some ci -> (
        match dispatch_positions ci meth with
        | [] -> vals (* 位置が取れなければ従来どおり全走査(組み込みの安全側) *)
        | ps -> List.filteri (fun i _ -> List.mem i ps) vals)
    | None -> vals
  in
  let find_impl v =
    match tycon_of_value v with
    | Some con -> (
        match Hashtbl.find_opt user_instances (cls_oid, con) with
        | Some methods -> (
            match List.assoc_opt (Type.intern meth) methods with Some f -> Some (fun args -> apply f args) | None -> None)
        | None -> Builtin.builtin_method cls_name (Type.name_of con) meth)
    | None -> None
  in
  match List.find_map find_impl cand_vals with
  | Some f -> f args
  | None -> (
      (* 構造的導出(v0 は Eq のみ、§8.2)。コヒーレンスにより elab の判定と必ず一致 *)
      let structural = match Decls.find_class cls_oid with Some ci -> ci.Decls.ci_derive_structural | None -> false in
      match (structural, meth, vals) with
      | true, "eq", [ a; b ] -> VBool (structural_eq a b)
      | _ ->
          runtime_error
            (cls_name ^ "." ^ meth ^ " のインスタンスが見つかりません: "
            ^ String.concat ", " (List.map show vals)))

and value_eq a b = Builtin.as_bool (dispatch "Eq" "eq" (VRecord [ (Type.l_item, a); (Type.l_item, b) ]))

(* レコードは「左のフィールドを順に、右から最左同名を取り出して消す」(§8.2。
   異ラベル間の物理順序は違いうるので単純な順序比較は誤り) *)
and structural_eq a b =
  match (a, b) with
  | VRecord fs1, VRecord _ ->
      let rec go fs1 rv =
        match fs1 with
        | [] -> record_fields rv = []
        | (l, x) :: rest -> (
            match record_take rv l with
            | y, rv' -> value_eq x y && go rest rv'
            | exception Runtime_error _ -> false)
      in
      go fs1 b
  | VVariant (l1, p1), VVariant (l2, p2) -> l1 = l2 && value_eq p1 p2
  | VData d1, VData d2 ->
      d1.d_type = d2.d_type && d1.d_ctor = d2.d_ctor
      && Array.length d1.d_fields = Array.length d2.d_fields
      && Array.for_all2 (fun x y -> value_eq x y) d1.d_fields d2.d_fields
  | (VClosure _ | VPrim _), _ | _, (VClosure _ | VPrim _) -> runtime_error "関数は比較できません"
  | _ -> value_eq a b

(* ---- let 束縛 ---- *)

and eval_binding_value env ((_, b) : T.let_binding) =
  match b.T.lb_params with
  | Some ps -> VClosure { c_env = env; c_params = ps; c_body = b.T.lb_body }
  | None -> eval env b.T.lb_body

and eval_binding env ((_, b) as bnode : T.let_binding) =
  let v = eval_binding_value env bnode in
  bind_pat_exn env.locals b.T.lb_name v

and eval_rec_bindings env (bs : T.let_binding list) =
  (* クロージャ生成 → 環境構築 → c_env バックパッチ(§8.2) *)
  let closures =
    List.map
      (fun ((_, b) : T.let_binding) ->
        let name = match snd b.T.lb_name with T.PVar x -> x | _ -> runtime_error "let rec は名前束縛のみです" in
        let c =
          match b.T.lb_params with
          | Some ps -> { c_env = env; c_params = ps; c_body = b.T.lb_body }
          | None -> (
              match snd b.T.lb_body with
              | T.Lambda { l_params; l_body } -> { c_env = env; c_params = l_params; c_body = l_body }
              | _ -> runtime_error "let rec の右辺は関数でなければなりません")
        in
        (name, c))
      bs
  in
  let locals = List.fold_left (fun locals (n, c) -> SMap.add n (VClosure c) locals) env.locals closures in
  List.iter (fun (_, c) -> c.c_env <- { env with locals }) closures;
  locals

(* ---- エフェクトハンドラ(§8.4。spike S2 のプロトコル) ---- *)

and eval_handle env body clauses =
  (* inst は Handle ノードの評価のたびに採番する(入れ子活性化が外側宛の Unwind を
     自分宛と誤認しないため。誤動作を spike で実測済み) *)
  let inst = new_oid () in
  let op_clauses =
    List.filter_map
      (fun (cl : T.clause) ->
        match Tree.get_resolved cl with Some (Tree.ROp op) -> Some (op, cl) | _ -> None)
      clauses
  in
  let ret_clause = List.find_opt (fun cl -> Tree.get_resolved cl = Some Tree.RReturnClause) clauses in
  let cancel_clause = List.find_opt (fun cl -> Tree.get_resolved cl = Some Tree.RCancelClause) clauses in
  let run_cancel () =
    match cancel_clause with
    | None -> ()
    | Some (_, c) -> (
        (* cancel 節内の例外は抑制してログ(sample.kel:392) *)
        try ignore (eval { env with resume = None } c.T.cl_body)
        with
        | Runtime_error msg -> !cancel_log msg
        | Unwind _ -> !cancel_log "cancel 節から操作の巻き戻しで脱出しようとしました"
        | ex -> !cancel_log (Printexc.to_string ex))
  in
  let clause_arg_pats (c : T.clause') =
    match snd c.T.cl_pat with T.PCtor (_, aps) -> List.map (fun (ap : T.ctor_arg_pat) -> ap.T.cap_pat) aps | _ -> []
  in
  Effect.Deep.match_with (fun () -> eval env body) ()
    {
      retc =
        (fun v ->
          (* return 節は親スタック上で走る(§8.4) *)
          match ret_clause with
          | None -> v
          | Some (_, c) ->
              let pat = match clause_arg_pats c with [ p ] -> p | _ -> bug "return 節のパターン" in
              let locals = bind_pat_exn env.locals pat v in
              eval { env with locals; resume = None } c.T.cl_body);
      exnc =
        (fun ex ->
          match ex with
          | Unwind (id, v) when id = inst -> v
          | ex ->
              (* 外側による巻き戻し(または実行時エラー)の通過: cancel 節を実行してから再送出 *)
              run_cancel ();
              raise ex);
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (op, args) -> (
              match List.find_opt (fun (o, _) -> o = op) op_clauses with
              | None -> None (* 自分の操作でなければ外側へ *)
              | Some (_, (_, c)) ->
                  Some
                    (fun (k : (a, _) Effect.Deep.continuation) ->
                      let pats = clause_arg_pats c in
                      let fields = record_fields args in
                      let locals =
                        List.fold_left2 (fun locals p (_, v) -> bind_pat_exn locals p v) env.locals pats fields
                      in
                      (match c.T.cl_guard with
                      | Some g ->
                          if not (Builtin.as_bool (eval { env with locals; resume = None } g)) then
                            runtime_error "ハンドラ節のガードが偽になりました(v0 ではガード付き操作節の後送りは未対応)"
                      | None -> ());
                      match snd c.T.cl_body with
                      | T.Resume arg ->
                          (* 末尾 resume 最適化(§8.4 の性能特性): continue を末尾発行する *)
                          let r = { r_k = k; r_used = true; r_alive = true } in
                          let v =
                            match arg with Some e -> eval { env with locals; resume = Some r } e | None -> unit
                          in
                          r.r_alive <- false;
                          Effect.Deep.continue k v
                      | _ -> (
                          let r = { r_k = k; r_used = false; r_alive = true } in
                          match eval { env with locals; resume = Some r } c.T.cl_body with
                          | v ->
                              r.r_alive <- false;
                              if r.r_used then v else Effect.Deep.discontinue k (Unwind (inst, v))
                          | exception ex ->
                              (* 節が例外で脱出したときも必ず discontinue(捨てた継続の中の
                                 cancel を走らせる。落とすと資源が漏れることを spike で実測済み) *)
                              r.r_alive <- false;
                              if r.r_used then raise ex else Effect.Deep.discontinue k ex)))
          | _ -> None);
    }

(* ---- トップレベル ---- *)

let register_builtin_values globals =
  let reg n f = Hashtbl.replace globals n (VPrim { p_name = n; p_fn = f }) in
  reg "Ref.new" (fun args -> VRef (ref (Builtin.arg1 args)));
  reg "Ref.get" (fun args -> match Builtin.arg1 args with VRef r -> !r | v -> runtime_error ("Ref ではありません: " ^ show v));
  reg "Ref.set" (fun args ->
      match Builtin.arg_values args with
      | [ VRef r; v ] ->
          r := v;
          unit
      | _ -> runtime_error "Ref.set の引数が不正です");
  reg "Array.new" (fun args ->
      match Builtin.arg_values args with
      | [ VInt32 n; init ] ->
          if Int32.to_int n < 0 then runtime_error "Array.new: 長さが負です" else VArray (Array.make (Int32.to_int n) init)
      | _ -> runtime_error "Array.new の引数が不正です");
  reg "Array.length" (fun args ->
      match Builtin.arg1 args with VArray a -> VInt32 (Int32.of_int (Array.length a)) | _ -> runtime_error "Array ではありません");
  reg "Array.get" (fun args ->
      match Builtin.arg_values args with
      | [ VArray a; VInt32 i ] ->
          let i = Int32.to_int i in
          if i < 0 || i >= Array.length a then runtime_error "配列の範囲外です" else a.(i)
      | _ -> runtime_error "Array.get の引数が不正です");
  reg "Array.set" (fun args ->
      match Builtin.arg_values args with
      | [ VArray a; VInt32 i; v ] ->
          let i = Int32.to_int i in
          if i < 0 || i >= Array.length a then runtime_error "配列の範囲外です"
          else (
            a.(i) <- v;
            unit)
      | _ -> runtime_error "Array.set の引数が不正です");
  reg "Array.each" (fun args ->
      match Builtin.arg_values args with
      | [ VArray a; f ] ->
          Array.iter (fun x -> ignore (apply f (VRecord [ (Type.l_item, x) ]))) a;
          unit
      | _ -> runtime_error "Array.each の引数が不正です")

(* クラスメソッドの識別子参照は dispatch へのラッパで素通しにする(§8.5) *)
let register_class_methods globals =
  Hashtbl.iter
    (fun _ (ci : Decls.class_info) ->
      let cls_name = Type.name_of ci.Decls.ci_name in
      List.iter
        (fun (m, _) ->
          let wrapper = VPrim { p_name = cls_name ^ "." ^ m; p_fn = (fun args -> dispatch cls_name m args) } in
          Hashtbl.replace globals m wrapper;
          Hashtbl.replace globals (cls_name ^ "." ^ m) wrapper)
        ci.Decls.ci_methods)
    Decls.classes

let exec_decl env ((_, d) : T.decl) =
  match d with
  | T.DLet ((_, b) as bnode) ->
      let v = eval_binding_value env bnode in
      let bound = bind_pat_exn SMap.empty b.T.lb_name v in
      SMap.iter (fun n v -> Hashtbl.replace env.globals n v) bound
  | T.DLetRec bs ->
      (* globals 共有なのでバックパッチ不要(名前解決は呼び出し時) *)
      List.iter
        (fun ((_, b) as bnode : T.let_binding) ->
          match snd b.T.lb_name with
          | T.PVar x -> Hashtbl.replace env.globals x (eval_binding_value env bnode)
          | _ -> runtime_error "let rec は名前束縛のみです")
        bs
  | T.DExp e -> ignore (eval env e)
  | T.DInstance i ->
      let cls = Type.intern i.T.ins_class in
      (* module 平坦化の同義語を通す(BigInt.BigInt 等。検証で発見)。
         組み込み(Add[Int32] 等)と同じキーのユーザ宣言は実体を差し替えない
         — elab は組み込みを使うので、実行時だけ差し替わるとコヒーレンスが破れる(検証で発見) *)
      let con =
        match i.T.ins_args with
        | [ (_, T.EIdent (LongId [ n ])) ] -> Decls.resolve_con (Type.intern n)
        | [ (_, T.EApply ((_, T.EIdent (LongId [ n ])), _)) ] -> Decls.resolve_con (Type.intern n)
        | _ -> bug "インスタンス頭が解決できません"
      in
      if
        (match Decls.find_class cls with Some ci -> ci.Decls.ci_builtin | None -> false)
        && Decls.builtin_instance_exists cls con
      then () (* 組み込みインスタンスは差し替えない(elab と一致させる) *)
      else
      let methods =
        List.concat_map
          (fun ((_, d) : T.decl) ->
            match d with
            | T.DLet ((_, b) as bnode) -> (
                match snd b.T.lb_name with
                | T.PVar x -> [ (Type.intern x, eval_binding_value env bnode) ]
                | _ -> [])
            | T.DLetRec bs ->
                let locals = eval_rec_bindings env bs in
                List.filter_map
                  (fun ((_, b) : T.let_binding) ->
                    match snd b.T.lb_name with
                    | T.PVar x -> Some (Type.intern x, SMap.find x locals)
                    | _ -> None)
                  bs
            | _ -> [])
          i.T.ins_body
      in
      Hashtbl.replace user_instances (cls, con) methods
  | T.DExtern ex ->
      let impl =
        match Builtin.find_prim ex.T.ex_name with
        | Some f -> f
        | None -> fun _ -> runtime_error ("未実装のプリミティブ: " ^ ex.T.ex_name)
      in
      Hashtbl.replace env.globals ex.T.ex_name (VPrim { p_name = ex.T.ex_name; p_fn = impl })
  | T.DType _ | T.DNewtype _ | T.DEffect _ | T.DClass _ -> ()
  | T.DModule _ -> runtime_error "module の評価は未実装です(M10)"

let run ~sink decls =
  Hashtbl.reset user_instances;
  Hashtbl.reset Builtin.fs;
  Hashtbl.reset Builtin.handles;
  let globals = Hashtbl.create 512 in
  register_builtin_values globals;
  register_class_methods globals;
  let env = { globals; locals = SMap.empty; resume = None } in
  ignore
    (Builtin.with_runtime ~sink (fun () ->
         List.iter (exec_decl env) decls;
         unit))
