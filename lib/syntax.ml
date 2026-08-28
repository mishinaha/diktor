(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *)
open Aux

type long_id = LongId of string list

let long_id components = LongId components

let show_long_id long_id =
  let (LongId components) = long_id in
  let rec aux out = function
    | [ h ] -> Buffer.add_string out h
    | h :: t ->
        Buffer.add_string out h;
        Buffer.add_string out "::";
        aux out t
    | [] -> failwith "Empty long_id"
  in
  let buf = Buffer.create 100 in
  aux buf components;
  Buffer.contents buf

module Type = struct
  type level = int

  let label_map : (string, oid) Hashtbl.t = Hashtbl.create 1024

  let label_oid_map : (oid, string) Hashtbl.t = Hashtbl.create 1024

  let label_to_oid label =
    match Hashtbl.find_opt label_map label with
    | Some oid -> oid
    | None ->
        let ret = new_oid () in
        Hashtbl.add label_map label ret;
        Hashtbl.add label_oid_map ret label;
        ret

  let oid_to_label oid = Hashtbl.find label_oid_map oid

  type ty =
    | TLongId of long_id
    | TApply of ty list * ty
    | TArrow of ty * ty
    | TTuple of ty list
    | TVar of tvar ref
    | TVariant of string list * string * (string * ty) list
    | TRecord of ty
    | TRowExtend of oid * ty * ty
    | TRowEmpty
    | TGiven of ty * ty

  and tvar = Unbound of int * level | Link of ty | Generic of int

  let new_var level = TVar (ref (Unbound (new_oid (), level)))

  let new_gen_var () = TVar (ref (Generic (new_oid ())))

  let i1 = TLongId (long_id [ "Orphos"; "Bool"; "t" ])

  let i8 = TLongId (long_id [ "Orphos"; "Int8"; "t" ])

  let i16 = TLongId (long_id [ "Orphos"; "Int16"; "t" ])

  let i32 = TLongId (long_id [ "Orphos"; "Int32"; "t" ])

  let i64 = TLongId (long_id [ "Orphos"; "Int64"; "t" ])

  let u8 = TLongId (long_id [ "Orphos"; "UInt8"; "t" ])

  let u16 = TLongId (long_id [ "Orphos"; "UInt16"; "t" ])

  let u32 = TLongId (long_id [ "Orphos"; "UInt32"; "t" ])

  let u64 = TLongId (long_id [ "Orphos"; "UInt64"; "t" ])

  let z = TLongId (long_id [ "Oprhos"; "Z"; "t" ])

  let text = TLongId (long_id [ "Oprhos"; "Text"; "t" ])

  let unit = TLongId (long_id [ "Orphos"; "Unit"; "t" ])

  let listType = TLongId (long_id [ "Orphos"; "List"; "t" ])

  let arrayType = TLongId (long_id [ "Orphos"; "Array"; "t" ])
end

type number_literal_type = ZType | QType | IntType of int | FloatType of int

(* 仮の表現: (仮数, 10のべきの分母指数)。M2 の D13(字句テキスト保持)で置き換える *)
type number = (int * int) * number_literal_type

type bin_op =
  | Add
  | Substract
  | Multiply
  | Division
  | Xor
  | Reminder
  | BitwiseLeftShift
  | BitwiseRightShift
  | Less
  | Greater
  | Equal
  | NotEqual
  | BitwiseAnd
  | And
  | BitwiseOr
  | Or
  | AddAsign
  | SubstractAsign
  | Asign
  | Combine
  | Remove
  | Cons
  | Append
  | Prepend
  | Erase
  | Dot

type prefix_op =
  | Positive
  | Negative
  | Not
  | Deref
  | Ref
  | Raise
  | Lazy
  | PrefixIncrement
  | PrefixDecrement
  | BitwiseNot

type postfix_op = PostfixIncrement | PostfixDecrement

type pat_bin_op = [ `Colon | `Comma | `At ]

module type Data = sig
  type t

  val allocate : unit -> t
end

module EmptyData : Data = struct
  type t = unit

  let allocate () = ()
end

module Make (Data : Data) = struct
  type exp' =
    | Bool of bool
    | Number of number
    | Text of string
    | Ident of long_id
    | Unit
    | Apply of exp * exp
    | BinOp of exp * bin_op * exp
    | PrefixOp of prefix_op * exp
    | PostfixOp of exp * postfix_op
    | Tuple of exp list
    | IfThenElse of exp * exp * exp option
    | Seq of exp list
    | Lambda of pat * exp
    | Let of pat * pat list * exp * exp
    | LetRec of (pat * pat list * exp) list * exp
    | Match of exp * pat_clause list
    | ListLiteral of exp list
    | ArrayLiteral of exp list
    | RecordEmpty
    | RecordExtend of exp * string * exp
    | RecordRestrictionLiteral of exp * string
    | RecordSelection of exp * string
    | PolymorphicVariantConstruction of string * exp
    | Handle of exp * pat_clause list
    | Construct of long_id * exp option

  and exp = Data.t * exp'

  and pat_clause' =
    | MatchPat of pat * exp option * exp
    | MatchException of pat * exp option * exp
    | MatchEffect of pat * exp option * exp

  and pat_clause = Data.t * pat_clause'

  and pat' =
    | PUnit
    | PCapture of string * pat
    | PCtor of string * pat
    | PTuple of pat list
    | PWildcard
    | PText of string
    | PNumber of number
    | PBool of bool
    | PLazy of pat
    | POr of pat * pat
    | PListLiteral of pat list
    | PArrayLiteral of pat list
    | PPolymorphicVariant of string * pat

  and pat = Data.t * pat'

  type type_exp' =
    | EIdent of long_id
    | EGeneric of string
    | ELazy of type_exp
    | ELabel of string * type_exp
    | EEff of type_exp * long_id list
    | ERecord of type_exp option * (string * type_exp) list
    | EPolymorphicVariant of string * type_exp
    | EOr of type_exp list
    | ERefinement of type_exp * exp list
    | EGiven of type_exp * long_id list
    | EArrow of type_exp * type_exp
    | ETuple of type_exp list
    | EApply of type_exp list * type_exp

  and type_exp = Data.t * type_exp'

  type ctor' = Ctor of string * type_exp

  type ctor = Data.t * ctor'

  type type_decl' =
    | TypeAlias of string list * string * type_exp
    | MonomorphicVariant of string list * string * ctor list
    | TypeDecl of string list * string
    | ValDef of string * type_exp
    | ExceptionDef of string * type_exp option

  type type_decl = Data.t * type_decl'

  type let_rec_def_part' = LetRecDefPart of pat * exp

  type let_rec_def_part = Data.t * let_rec_def_part'

  type module_part' = TypeDeclInModule of type_decl | LetDef of pat * exp | LetRecDef of let_rec_def_part list

  type module_part = Data.t * module_part'

  type interface_exp = type_decl list * (string list * string * type_exp) list

  type interface_ref' = InterfaceExp of interface_exp | InterfaceId of long_id

  type interface_ref = Data.t * interface_ref'

  type module_exp = module_part list * interface_ref list

  type decl' =
    | InterfaceDecl of string * bool * interface_exp
    | ModuleDecl of string option * bool * module_exp
    | FunctorDecl of string * (string * interface_ref) list * module_exp

  type decl = Data.t * decl'

  type compilation_unit' = CompilationUnit of decl list

  type compilation_unit = Data.t * compilation_unit'
end
