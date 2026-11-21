(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第20章 KIR のバイナリ

   本章は、第17章の `Ir.program` をバイナリ(`.kir`)に符号化し、
   バイナリを読んで `Ir.program` に戻す。
   仕様は親リポジトリの `doc/IRSpec.md` の 13 節が定める。
   RustKeleut のリーダ(reader)とライタ(writer)も、バイナリをバイト単位で一致するように読み書きする。
   そのため、本章が書く値の順序と番号は、IRSpec の表に合わせてある。

   バイナリとテキストは 1 対 1 に対応し、相互に変換できる(ラウンドトリップ)。
   テキストにないものは、strings の表、blobs の表、prims の表と、表の項目を指す添字である。
   本章は、これらをテキストの内容だけから決まる規則で作る。

   | バイナリにだけあるもの | 作り方 |
   |---|---|
   | strings の表 | 名前の集まりを、バイト列の昇順に並べたもの |
   | blobs の表 | 文字列リテラルと元のファイルのパスの集まりを、バイト列の昇順に並べたもの |
   | prims の表 | `extern` のグローバルの ABI と実装名の組の集まりを、ABI の番号と実装名の順に並べたもの |
   | 表の項目への参照 | その表の中の位置 |

   読み込みは、形式のエラーをすべて `Error` のメッセージにして返し、例外を外へ出さない。
   壊れたファイルを読んでも処理系が異常終了しないことを、リーダが保証するためである。
   読み込みが検査するのは、バイトの並び、バージョン、セクションの順序とサイズ、添字の範囲、
   表の項目の順序である。
   参照の種類の整合や末尾の印のような意味の検査は、第21章の検証器が `Ir.program` に対して行う。 *)
open Ir

(* ## 20.1 番号

   ヘッダは 16 バイトで、マジックナンバー、メジャーバージョン、マイナーバージョン、必須機能ビット、
   セクションの個数からなる。
   必須のセクションは id が 0x01 から 0x0B の 11 個で、本章のライタはこの 11 個だけを書く。
   id が 0x80 以上のセクションはスキップできるセクションであり、リーダは内容を読まずに飛ばす。 *)
let magic = "\000KIR"

let sec_strings = 0x01

let sec_blobs = 0x02

let sec_units = 0x03

let sec_types = 0x04

let sec_effects = 0x05

let sec_classes = 0x06

let sec_instances = 0x07

let sec_prims = 0x08

let sec_globals = 0x09

let sec_functions = 0x0A

let sec_init = 0x0B

(* 入れ子の上限 `max_nest` は、式、辞書、パターンのノードに許す最大の深さである。
   関数の本体、ガード、操作節の各パターン、`def_pattern` のパターンを深さ 1 とし、
   子のノードは親より 1 深い。
   リーダは、深さがこの値を超えるファイルを拒否する。
   値は、20,000 段の `1 + (...)` のような深い式を持つプログラムの深さより十分に大きくしてある。 *)
let max_nest = 100_000

(* KIR は、各構文に 1 バイトの番号を割り当てる。
   どの位置にどの番号空間の番号が来るかは文法から決まるので、
   式、辞書、パターン、初期化手順、グローバルの種類は、それぞれ別の番号空間を持つ。
   以下の関数と配列は、Rep、関数の種類、操作節の分類、ABI の番号を定める。 *)
let rep_code = function RBool -> 0 | RI32 -> 1 | RI64 -> 2 | RF64 -> 3 | RStr -> 4 | RAny -> 5

let rep_of_code = [| RBool; RI32; RI64; RF64; RStr; RAny |]

let kind_code = function
  | Lambda -> 0
  | Opclause -> 1
  | Retclause -> 2
  | Cancelclause -> 3
  | Handlebody -> 4
  | Thunk -> 5
  | Dictabs_fn -> 6

let kind_of_code = [| Lambda; Opclause; Retclause; Cancelclause; Handlebody; Thunk; Dictabs_fn |]

let class_code = function N -> 0 | T -> 1 | G -> 2

let class_of_code = [| N; T; G |]

let abi_code = function Prim -> 0 | C -> 1

let abi_of_code = [| Prim; C |]

(* ## 20.2 書き出しの基本のエンコーディング

   整数は、個数、添字、スロットの番号を uLEB128 で書き、`i32` と `i64` の値を sLEB128 で書く。
   ライタは常に最短のエンコーディングで書く。
   `f64` はビット列を 8 バイトのリトルエンディアンで書くので、NaN のペイロードも保たれる。
   バイト列は、長さの uLEB128 に内容を続けて書く。

   符号化のエラーは 2 種類ある。
   `Name_error` は、プログラムが UTF-8 でない名前を持つときのエラーで、原因は入力にある。
   `Encode_error` は、表にない名前を参照するなどのエラーで、原因は KIR を書き出す側のバグにある。
   呼び出し元が終了コードを分けられるように、例外を分けている。 *)
exception Encode_error of string

exception Name_error of string

let put_u8 b n = Buffer.add_char b (Char.chr n)

let put_u16 b n =
  put_u8 b (n land 0xff);
  put_u8 b ((n lsr 8) land 0xff)

let put_u32 b n =
  put_u16 b (n land 0xffff);
  put_u16 b ((n lsr 16) land 0xffff)

let rec put_uleb b n =
  if n < 0x80 then put_u8 b n
  else (
    put_u8 b (n land 0x7f lor 0x80);
    put_uleb b (n lsr 7))

(* sLEB128 は、残りの値が符号拡張だけになり、
   最後のバイトの第 6 ビットがその符号と一致したところで止める *)
let rec put_sleb b (n : int64) =
  let byte = Int64.to_int (Int64.logand n 0x7fL) in
  let rest = Int64.shift_right n 7 in
  if (rest = 0L && byte land 0x40 = 0) || (rest = -1L && byte land 0x40 <> 0) then put_u8 b byte
  else (
    put_u8 b (byte lor 0x80);
    put_sleb b rest)

let put_f64 b (bits : int64) =
  for i = 0 to 7 do
    put_u8 b (Int64.to_int (Int64.logand (Int64.shift_right_logical bits (8 * i)) 0xffL))
  done

let put_bytes b s =
  put_uleb b (String.length s);
  Buffer.add_string b s

let put_vec b f xs =
  put_uleb b (List.length xs);
  List.iter f xs

(* ## 20.3 表を集める

   strings の表に入るのは、シンボル、コンストラクタと操作とメソッドの名前、ラベル、単位のキー、
   `extern` の実装名、範囲外のリテラルの表記である。
   blobs の表に入るのは、式とパターンの文字列リテラルと、単位の元のファイルのパスである。
   ファイルのパスは UTF-8 とは限らないので、任意のバイト列を置ける blobs の表に入れる。
   strings の表の名前は UTF-8 でなければならない。
   ライタは、UTF-8 でない名前を見つけたら `Name_error` を投げて符号化をやめる。

   どちらの表も、項目の集まりから重複を取り除き、バイト列の昇順に並べたものである。
   OCaml の `String.compare` は、共通の先頭部分のバイトを符号なしで比べ、
   そこまで等しければ短いほうを先にするので、
   この順序と一致する。 *)
module SSet = Set.Make (String)

let rec lits_of_pat strs blobs = function
  | PWild | PBind _ -> ()
  | PLit (LStr s) -> blobs := SSet.add s !blobs
  | PLit _ -> ()
  | PRecord (fs, tl) -> (
      List.iter
        (fun (l, p) ->
          strs := SSet.add l !strs;
          lits_of_pat strs blobs p)
        fs;
      match tl with Rest p -> lits_of_pat strs blobs p | Closed | Open -> ())
  | PCtor (_, _, fs) -> List.iter (fun (_, p) -> lits_of_pat strs blobs p) fs
  | PVariant (l, p) ->
      strs := SSet.add l !strs;
      lits_of_pat strs blobs p

let rec names_of_dict strs = function
  | DInst (_, ps) -> List.iter (names_of_dict strs) ps
  | DVar _ | DBuiltin _ -> ()
  | DRecord fs | DVariant fs ->
      List.iter
        (fun (l, d) ->
          strs := SSet.add l !strs;
          names_of_dict strs d)
        fs

let rec names_of_exp strs blobs e =
  let ex = names_of_exp strs blobs in
  let label l = strs := SSet.add l !strs in
  match e with
  | Lit (LStr s) -> blobs := SSet.add s !blobs
  | Lit _ | Local _ | Env _ | Global _ | Closure _ | Dictabs _ | Rec_empty | Hole -> ()
  | Lit_error (_, s) -> label s
  | Construct (_, _, fs) -> List.iter (fun (_, e) -> ex e) fs
  | Variant (l, e) | Rec_select (l, e) | Rec_restrict (l, e) ->
      label l;
      ex e
  | Call c -> List.iter ex (c.c_fn :: c.c_args)
  | Method (_, _, d, os) -> List.iter (names_of_dict strs) (d :: os)
  | Opcall (_, _, d, args) ->
      names_of_dict strs d;
      List.iter ex args
  | Not e -> ex e
  | And (a, b) | Or (a, b) | Let (_, a, b) ->
      ex a;
      ex b
  | Dictapp (e, ds) ->
      ex e;
      List.iter (names_of_dict strs) ds
  | Letpat (p, a, b) ->
      lits_of_pat strs blobs p;
      ex a;
      ex b
  | Letrec (items, e) ->
      List.iter (fun (_, e) -> ex e) items;
      ex e
  | Seq es -> List.iter ex es
  | Match (e, cls) ->
      ex e;
      List.iter
        (fun c ->
          lits_of_pat strs blobs c.cl_pat;
          Option.iter ex c.cl_guard;
          ex c.cl_body)
        cls
  | Rec_extend (l, a, b) | Rec_update (l, a, b) ->
      label l;
      ex a;
      ex b
  | Perform (_, _, args) -> List.iter ex args
  | Handle _ -> ()
  | Resume (_, e) -> ex e

let collect (p : program) =
  let strs = ref SSet.empty and blobs = ref SSet.empty in
  let add s = strs := SSet.add s !strs in
  List.iter
    (fun u ->
      add u.u_key;
      List.iter (fun s -> blobs := SSet.add s !blobs) u.u_paths;
      List.iter (function Def_pattern (_, _, pat) -> lits_of_pat strs blobs pat | _ -> ()) u.u_init)
    p.units;
  List.iter
    (fun t ->
      add t.t_sym;
      List.iter (fun c -> add c.ct_name) t.t_ctors)
    p.types;
  List.iter
    (fun e ->
      add e.e_sym;
      List.iter (fun o -> add o.o_name) e.e_ops)
    p.effects;
  List.iter
    (fun c ->
      add c.c_sym;
      List.iter (fun (m, _) -> add m) c.c_methods)
    p.classes;
  List.iter (fun i -> add i.i_sym) p.instances;
  List.iter (fun g -> add g.g_sym; match g.g_kind with GExtern { impl; _ } -> add impl | _ -> ()) p.globals;
  List.iter
    (fun f ->
      add f.f_sym;
      List.iter (lits_of_pat strs blobs) f.f_pats;
      Option.iter (names_of_exp strs blobs) f.f_guard;
      names_of_exp strs blobs f.f_body)
    p.functions;
  SSet.iter (fun s -> if not (String.is_valid_utf_8 s) then raise (Name_error ("UTF-8 でない名前があります: " ^ String.escaped s))) !strs;
  (SSet.elements !strs, SSet.elements !blobs)

(* prims の表の項目は、ABI と実装名の組である。
   項目は ABI の番号(`prim` が 0、`C` が 1)の順に並べ、
   同じ ABI の中では実装名のバイト列の昇順に並べる。 *)
let prims_of (p : program) =
  let key (a, s) = (abi_code a, s) in
  let all = List.filter_map (fun g -> match g.g_kind with GExtern { abi; impl; _ } -> Some (abi, impl) | _ -> None) p.globals in
  List.sort_uniq (fun x y -> compare (key x) (key y)) all

(* ## 20.4 添字

   表の項目は、その表の中の位置(0 始まり)で指す。
   コンストラクタ、操作、メソッドは、それを持つ型、エフェクト、クラスの中の位置で指す。
   ライタは、名前から位置を求めるハッシュ表を表ごとに作る。
   このハッシュ表は検索にだけ使い、走査には使わないので、
   出力の順序はハッシュ表の内部の順序によらない。 *)
let index_of names =
  let h = Hashtbl.create (List.length names * 2 + 1) in
  List.iteri (fun i s -> if not (Hashtbl.mem h s) then Hashtbl.replace h s i) names;
  h

let find what h k = match Hashtbl.find_opt h k with Some i -> i | None -> raise (Encode_error (what ^ "が表にありません: " ^ k))

type enc = {
  b : Buffer.t;
  str : (string, int) Hashtbl.t;
  blob : (string, int) Hashtbl.t;
  ty : (string, int) Hashtbl.t;
  ctor : (string * string, int) Hashtbl.t;
  eff : (string, int) Hashtbl.t;
  op : (string * string, int) Hashtbl.t;
  cls : (string, int) Hashtbl.t;
  meth : (string * string, int) Hashtbl.t;
  inst : (string, int) Hashtbl.t;
  prim : (abi * string, int) Hashtbl.t;
  glob : (string, int) Hashtbl.t;
  fn : (string, int) Hashtbl.t;
}

let inner_index items =
  let h = Hashtbl.create 64 in
  List.iter (fun (owner, names) -> List.iteri (fun i n -> if not (Hashtbl.mem h (owner, n)) then Hashtbl.replace h (owner, n) i) names) items;
  h

let find2 what h (o, n) = match Hashtbl.find_opt h (o, n) with Some i -> i | None -> raise (Encode_error (what ^ "が表にありません: " ^ o ^ " の " ^ n))

(* ## 20.5 式、辞書、パターンのエンコーディング

   各ノードは、1 バイトの番号と、決まった順序のフィールドからなる。
   リーダが先頭から 1 回読むだけで木を作れるように、子の個数は子より前に書く。

   リテラルは、式とパターンで同じ形式である。
   種類を表す 1 バイト(偽、真、`i32`、`i64`、`f64`、`str` の順に 0 から 5)を書き、
   偽と真以外の種類では、その後に値を書く。 *)
let put_str e s = put_uleb e.b (find "名前" e.str s)

let put_lit e = function
  | LBool false -> put_u8 e.b 0
  | LBool true -> put_u8 e.b 1
  | LI32 n ->
      put_u8 e.b 2;
      put_sleb e.b (Int64.of_int32 n)
  | LI64 n ->
      put_u8 e.b 3;
      put_sleb e.b n
  | LF64 bits ->
      put_u8 e.b 4;
      put_f64 e.b bits
  | LStr s ->
      put_u8 e.b 5;
      put_uleb e.b (find "文字列" e.blob s)

let put_var e = function
  | VLocal i ->
      put_u8 e.b 0;
      put_uleb e.b i
  | VEnv i ->
      put_u8 e.b 1;
      put_uleb e.b i
  | VDParam i ->
      put_u8 e.b 2;
      put_uleb e.b i

let rec put_dict e = function
  | DInst (i, ps) ->
      put_u8 e.b 0;
      put_uleb e.b (find "インスタンス" e.inst i);
      put_vec e.b (put_dict e) ps
  | DVar (VDParam i) ->
      put_u8 e.b 1;
      put_uleb e.b i
  | DVar (VEnv i) ->
      put_u8 e.b 2;
      put_uleb e.b i
  | DVar (VLocal _) -> raise (Encode_error "辞書の式にスロットがあります")
  | DRecord fs ->
      put_u8 e.b 3;
      put_dict_fields e fs
  | DVariant fs ->
      put_u8 e.b 4;
      put_dict_fields e fs
  | DBuiltin (c, t) ->
      put_u8 e.b 5;
      put_uleb e.b (find "クラス" e.cls c);
      put_uleb e.b (find "型" e.ty t)

and put_dict_fields e fs =
  put_vec e.b
    (fun (l, d) ->
      put_str e l;
      put_dict e d)
    fs

let rec put_pat e = function
  | PWild -> put_u8 e.b 0
  | PBind i ->
      put_u8 e.b 1;
      put_uleb e.b i
  | PLit l ->
      put_u8 e.b 2;
      put_lit e l
  | PRecord (fs, tl) -> (
      put_u8 e.b 3;
      put_u8 e.b (match tl with Closed -> 0 | Open -> 1 | Rest _ -> 2);
      put_vec e.b
        (fun (l, p) ->
          put_str e l;
          put_pat e p)
        fs;
      match tl with Rest p -> put_pat e p | Closed | Open -> ())
  | PCtor (t, c, fs) ->
      put_u8 e.b 4;
      put_uleb e.b (find "型" e.ty t);
      put_uleb e.b (find2 "コンストラクタ" e.ctor (t, c));
      put_vec e.b
        (fun (i, p) ->
          put_uleb e.b i;
          put_pat e p)
        fs
  | PVariant (l, p) ->
      put_u8 e.b 5;
      put_str e l;
      put_pat e p

let put_part e p =
  put_uleb e.b (find "関数" e.fn p.p_fn);
  put_vec e.b (put_var e) p.p_caps

let bit b n = if b then n else 0

let rec put_exp e x =
  let b = e.b in
  let ex = put_exp e in
  match x with
  | Lit l ->
      put_u8 b 0x00;
      put_lit e l
  | Lit_error (Lit_range, s) ->
      put_u8 b 0x01;
      put_u8 b 0;
      put_str e s
  | Local i ->
      put_u8 b 0x02;
      put_uleb b i
  | Env i ->
      put_u8 b 0x03;
      put_uleb b i
  | Global g ->
      put_u8 b 0x04;
      put_uleb b (find "グローバル" e.glob g)
  | Construct (t, c, fs) ->
      put_u8 b 0x05;
      put_uleb b (find "型" e.ty t);
      put_uleb b (find2 "コンストラクタ" e.ctor (t, c));
      put_vec b
        (fun (i, x) ->
          put_uleb b i;
          ex x)
        fs
  | Variant (l, x) ->
      put_u8 b 0x06;
      put_str e l;
      ex x
  | Call c ->
      put_u8 b 0x07;
      put_u8 b (bit c.c_tail 1 lor bit c.c_yield 2);
      put_uleb b (List.length c.c_args);
      ex c.c_fn;
      List.iter ex c.c_args
  | Method (c, m, d, os) ->
      put_u8 b 0x08;
      put_uleb b (find "クラス" e.cls c);
      put_uleb b (find2 "メソッド" e.meth (c, m));
      put_uleb b (List.length os);
      put_dict e d;
      List.iter (put_dict e) os
  | Opcall (c, m, d, args) ->
      put_u8 b 0x09;
      put_uleb b (find "クラス" e.cls c);
      put_uleb b (find2 "メソッド" e.meth (c, m));
      put_uleb b (List.length args);
      put_dict e d;
      List.iter ex args
  | Not x ->
      put_u8 b 0x0A;
      ex x
  | And (x, y) ->
      put_u8 b 0x0B;
      ex x;
      ex y
  | Or (x, y) ->
      put_u8 b 0x0C;
      ex x;
      ex y
  | Closure (f, cs) ->
      put_u8 b 0x0D;
      put_part e { p_fn = f; p_caps = cs }
  | Dictabs (f, cs) ->
      put_u8 b 0x0E;
      put_part e { p_fn = f; p_caps = cs }
  | Dictapp (x, ds) ->
      put_u8 b 0x0F;
      put_uleb b (List.length ds);
      ex x;
      List.iter (put_dict e) ds
  | Let (i, x, y) ->
      put_u8 b 0x10;
      put_uleb b i;
      ex x;
      ex y
  | Letpat (p, x, y) ->
      put_u8 b 0x11;
      put_pat e p;
      ex x;
      ex y
  | Letrec (items, x) ->
      put_u8 b 0x12;
      put_vec b
        (fun (i, x) ->
          put_uleb b i;
          ex x)
        items;
      ex x
  | Seq xs ->
      put_u8 b 0x13;
      put_vec b ex xs
  | Match (x, cls) ->
      put_u8 b 0x14;
      put_uleb b (List.length cls);
      ex x;
      List.iter
        (fun c ->
          put_u8 b (if c.cl_guard = None then 0 else 1);
          put_pat e c.cl_pat;
          Option.iter ex c.cl_guard;
          ex c.cl_body)
        cls
  | Rec_empty -> put_u8 b 0x15
  | Rec_extend (l, v, r) ->
      put_u8 b 0x16;
      put_str e l;
      ex v;
      ex r
  | Rec_select (l, x) ->
      put_u8 b 0x17;
      put_str e l;
      ex x
  | Rec_restrict (l, x) ->
      put_u8 b 0x18;
      put_str e l;
      ex x
  | Rec_update (l, r, v) ->
      put_u8 b 0x19;
      put_str e l;
      ex r;
      ex v
  | Perform (ef, op, args) ->
      put_u8 b 0x1A;
      put_uleb b (find "エフェクト" e.eff ef);
      put_uleb b (find2 "操作" e.op (ef, op));
      put_vec b ex args
  | Handle h ->
      put_u8 b 0x1B;
      put_u8 b (bit h.h_tail 1 lor bit (h.h_return <> None) 2 lor bit (h.h_cancel <> None) 4);
      put_uleb b (find "エフェクト" e.eff h.h_effect);
      put_uleb b (List.length h.h_ops);
      put_part e h.h_body;
      List.iter
        (fun (op, cls, p) ->
          put_uleb b (find2 "操作" e.op (h.h_effect, op));
          put_u8 b (class_code cls);
          put_part e p)
        h.h_ops;
      Option.iter (put_part e) h.h_return;
      Option.iter (put_part e) h.h_cancel
  | Resume (t, x) ->
      put_u8 b 0x1C;
      put_u8 b (bit t 1);
      ex x
  | Hole -> put_u8 b 0x1D

(* ## 20.6 セクションのエンコーディング

   各セクションの内容は次のとおりである。
   `vec(X)` は、個数の uLEB128 に X を個数だけ続けたものを表す。

   | セクション | 内容 |
   |---|---|
   | strings | `vec(バイト列)` |
   | blobs | `vec(バイト列)` |
   | units | `vec(キー, vec(元のファイルのパスの blob))` |
   | types | `vec(シンボル, vec(コンストラクタの名前, フィールドの個数))` |
   | effects | `vec(シンボル, vec(操作の名前, 引数の個数, 操作の印))` |
   | classes | `vec(シンボル, vec(メソッドの名前, メソッド自身の辞書の個数))` |
   | instances | `vec(シンボル, クラス, 対象の型の先頭の型構成子, 前提の個数, vec(メソッド, 辞書の個数, 関数))` |
   | prims | `vec(ABI, 実装名)` |
   | globals | `vec(シンボル, 種類, 種類ごとのフィールド)` |
   | functions | 関数の個数、シンボルを関数の個数だけ、関数の項目を関数の個数だけ |
   | init | `vec(vec(初期化手順))`。外側の並びは units のセクションと同じ順序で、同じ個数である |

   操作の印は 1 バイトで、`never` の 1 と `runtime` の 2 のうち、操作に付いているものの和である。
   functions のセクションは、シンボルの並びを関数の項目より前に置く。
   グローバル、インスタンス、関数の本体は、自分より後ろに現れる関数を指すことがある。
   リーダは、シンボルの並びを先に読めば、
   どのセクションを読むときも関数の添字をシンボルに変換できる。 *)
let put_step e = function
  | Def_value (g, f) ->
      put_u8 e.b 0;
      put_uleb e.b (find "グローバル" e.glob g);
      put_uleb e.b (find "関数" e.fn f)
  | Def_pattern (f, gs, p) ->
      put_u8 e.b 1;
      put_uleb e.b (find "関数" e.fn f);
      put_vec e.b (fun g -> put_uleb e.b (find "グローバル" e.glob g)) gs;
      put_pat e p
  | Def_fns gs ->
      put_u8 e.b 2;
      put_vec e.b (fun g -> put_uleb e.b (find "グローバル" e.glob g)) gs
  | Def_dictabs g ->
      put_u8 e.b 3;
      put_uleb e.b (find "グローバル" e.glob g)
  | Def_instance i ->
      put_u8 e.b 4;
      put_uleb e.b (find "インスタンス" e.inst i)
  | Run_exp f ->
      put_u8 e.b 5;
      put_uleb e.b (find "関数" e.fn f)

let put_global e g =
  put_str e g.g_sym;
  match g.g_kind with
  | GBuiltin -> put_u8 e.b 0
  | GExtern { abi; impl; dicts } ->
      put_u8 e.b 1;
      put_uleb e.b (Hashtbl.find e.prim (abi, impl));
      put_uleb e.b dicts
  | GFn f ->
      put_u8 e.b 2;
      put_uleb e.b (find "関数" e.fn f)
  | GDictabs f ->
      put_u8 e.b 3;
      put_uleb e.b (find "関数" e.fn f)
  | GValue r ->
      put_u8 e.b 4;
      put_u8 e.b (rep_code r)

(* 関数の項目は、種類、`yield` の印、引数の Rep の並び、ローカルの Rep の並び、辞書の引数の個数、
   キャプチャの Rep の並び、結果の Rep の順に並ぶ。
   種類が `opclause` の関数だけは、その後にパターンの並びと、ガードの有無を表す 1 バイトを持ち、
   ガードがあればその式が続く。
   最後に本体の式を書く。 *)
let put_fn e f =
  let b = e.b in
  let reps rs = put_vec b (fun r -> put_u8 b (rep_code r)) rs in
  put_u8 b (kind_code f.f_kind);
  put_u8 b (bit f.f_yield 1);
  reps f.f_params;
  reps f.f_locals;
  put_uleb b f.f_dicts;
  reps f.f_caps;
  put_u8 b (rep_code f.f_result);
  (if f.f_kind = Opclause then (
     put_vec b (put_pat e) f.f_pats;
     match f.f_guard with
     | None -> put_u8 b 0
     | Some g ->
         put_u8 b 1;
         put_exp e g)
   else if f.f_pats <> [] || f.f_guard <> None then raise (Encode_error ("操作節でない関数がパターンかガードを持ちます: " ^ f.f_sym)));
  put_exp e f.f_body

(* ## 20.7 書き出し

   ヘッダに書くセクションの個数は、実際に書くセクションの個数(常に 11)である。
   各セクションは、id の 1 バイト、内容のサイズの uLEB128、内容の順に書く。
   内容のサイズは書き終えるまで分からないので、セクションごとに別のバッファに内容を作ってから書く。

   どのリーダも、ノードの深さが入れ子の上限を超えるファイルを拒否する。
   そのため、ライタはそのようなプログラムを書かない。
   深さは読み込みと同じ規則で数え、何かを書く前に検査する。
   上限を超えたら、その場で `Limit_error` を投げ、それより深くはたどらない。
   たどる深さが上限で止まるので、検査に使うスタックも上限の深さの分で済む。 *)
exception Limit_error of string

let check_depth ?(max_nest = max_nest) (p : program) =
  let nest d = if d > max_nest then raise (Limit_error "処理系の限度: KIR の書き出しで入れ子が深すぎます") in
  let rec dict d x =
    nest d;
    match x with
    | DInst (_, ps) -> List.iter (dict (d + 1)) ps
    | DRecord fs | DVariant fs -> List.iter (fun (_, x) -> dict (d + 1) x) fs
    | DVar _ | DBuiltin _ -> ()
  in
  let rec pat d x =
    nest d;
    match x with
    | PWild | PBind _ | PLit _ -> ()
    | PRecord (fs, tl) -> (
        List.iter (fun (_, p) -> pat (d + 1) p) fs;
        match tl with Rest p -> pat (d + 1) p | Closed | Open -> ())
    | PCtor (_, _, fs) -> List.iter (fun (_, p) -> pat (d + 1) p) fs
    | PVariant (_, p) -> pat (d + 1) p
  in
  let rec exp d x =
    nest d;
    let ex = exp (d + 1) in
    let dc = dict (d + 1) in
    match x with
    | Lit _ | Lit_error _ | Local _ | Env _ | Global _ | Closure _ | Dictabs _ | Rec_empty | Handle _ | Hole -> ()
    | Construct (_, _, fs) -> List.iter (fun (_, x) -> ex x) fs
    | Variant (_, x) | Not x | Rec_select (_, x) | Rec_restrict (_, x) | Resume (_, x) -> ex x
    | Call c ->
        ex c.c_fn;
        List.iter ex c.c_args
    | Method (_, _, dd, os) ->
        dc dd;
        List.iter dc os
    | Opcall (_, _, dd, args) ->
        dc dd;
        List.iter ex args
    | And (x, y) | Or (x, y) | Let (_, x, y) | Rec_extend (_, x, y) | Rec_update (_, x, y) ->
        ex x;
        ex y
    | Dictapp (x, ds) ->
        ex x;
        List.iter dc ds
    | Letpat (q, x, y) ->
        pat (d + 1) q;
        ex x;
        ex y
    | Letrec (items, x) ->
        List.iter (fun (_, x) -> ex x) items;
        ex x
    | Seq xs | Perform (_, _, xs) -> List.iter ex xs
    | Match (x, cls) ->
        ex x;
        List.iter
          (fun c ->
            pat (d + 1) c.cl_pat;
            Option.iter ex c.cl_guard;
            ex c.cl_body)
          cls
  in
  List.iter
    (fun f ->
      List.iter (pat 1) f.f_pats;
      Option.iter (exp 1) f.f_guard;
      exp 1 f.f_body)
    p.functions;
  List.iter (fun u -> List.iter (function Def_pattern (_, _, q) -> pat 1 q | _ -> ()) u.u_init) p.units

let encode_exn (p : program) =
  check_depth p;
  let strs, blobs = collect p in
  let prims = prims_of p in
  let fresh () = Buffer.create 4096 in
  let e =
    {
      b = fresh ();
      str = index_of strs;
      blob = index_of blobs;
      ty = index_of (List.map (fun t -> t.t_sym) p.types);
      ctor = inner_index (List.map (fun t -> (t.t_sym, List.map (fun c -> c.ct_name) t.t_ctors)) p.types);
      eff = index_of (List.map (fun x -> x.e_sym) p.effects);
      op = inner_index (List.map (fun x -> (x.e_sym, List.map (fun o -> o.o_name) x.e_ops)) p.effects);
      cls = index_of (List.map (fun c -> c.c_sym) p.classes);
      meth = inner_index (List.map (fun c -> (c.c_sym, List.map fst c.c_methods)) p.classes);
      inst = index_of (List.map (fun i -> i.i_sym) p.instances);
      prim = (let h = Hashtbl.create 64 in List.iteri (fun i k -> Hashtbl.replace h k i) prims; h);
      glob = index_of (List.map (fun g -> g.g_sym) p.globals);
      fn = index_of (List.map (fun f -> f.f_sym) p.functions);
    }
  in
  let sections = ref [] in
  let section id f =
    let e = { e with b = fresh () } in
    f e;
    sections := (id, Buffer.contents e.b) :: !sections
  in
  section sec_strings (fun e -> put_vec e.b (put_bytes e.b) strs);
  section sec_blobs (fun e -> put_vec e.b (put_bytes e.b) blobs);
  section sec_units (fun e ->
      put_vec e.b
        (fun u ->
          put_str e u.u_key;
          put_vec e.b (fun s -> put_uleb e.b (find "文字列" e.blob s)) u.u_paths)
        p.units);
  section sec_types (fun e ->
      put_vec e.b
        (fun t ->
          put_str e t.t_sym;
          put_vec e.b
            (fun c ->
              put_str e c.ct_name;
              put_uleb e.b c.ct_arity)
            t.t_ctors)
        p.types);
  section sec_effects (fun e ->
      put_vec e.b
        (fun x ->
          put_str e x.e_sym;
          put_vec e.b
            (fun o ->
              put_str e o.o_name;
              put_uleb e.b o.o_arity;
              put_u8 e.b (bit o.o_never 1 lor bit o.o_runtime 2))
            x.e_ops)
        p.effects);
  section sec_classes (fun e ->
      put_vec e.b
        (fun c ->
          put_str e c.c_sym;
          put_vec e.b
            (fun (m, k) ->
              put_str e m;
              put_uleb e.b k)
            c.c_methods)
        p.classes);
  section sec_instances (fun e ->
      put_vec e.b
        (fun i ->
          put_str e i.i_sym;
          put_uleb e.b (find "クラス" e.cls i.i_class);
          put_uleb e.b (find "型" e.ty i.i_head);
          put_uleb e.b i.i_premises;
          put_vec e.b
            (fun (m, k, f) ->
              put_uleb e.b (find2 "メソッド" e.meth (i.i_class, m));
              put_uleb e.b k;
              put_uleb e.b (find "関数" e.fn f))
            i.i_methods)
        p.instances);
  section sec_prims (fun e ->
      put_vec e.b
        (fun (abi, impl) ->
          put_u8 e.b (abi_code abi);
          put_str e impl)
        prims);
  section sec_globals (fun e -> put_vec e.b (put_global e) p.globals);
  section sec_functions (fun e ->
      put_uleb e.b (List.length p.functions);
      List.iter (fun f -> put_str e f.f_sym) p.functions;
      List.iter (put_fn e) p.functions);
  section sec_init (fun e -> put_vec e.b (fun u -> put_vec e.b (put_step e) u.u_init) p.units);
  let sections = List.rev !sections in
  let out = Buffer.create 65536 in
  let major, minor = p.version in
  Buffer.add_string out magic;
  put_u16 out major;
  put_u16 out minor;
  put_u32 out 0;
  put_u32 out (List.length sections);
  List.iter
    (fun (id, payload) ->
      put_u8 out id;
      put_bytes out payload)
    sections;
  Buffer.contents out

let encode p =
  match encode_exn p with
  | s -> Ok s
  | exception (Encode_error msg | Name_error msg | Limit_error msg) -> Error ("KIR を符号化できません: " ^ msg)

(* ## 20.8 読み込みの基本のエンコーディング

   読み込みは、文字列 `src` を位置 `pos` から後ろへ順に読む。
   各セクションを読むときは、読み取りの終端 `stop` をそのセクションの終わりに設定し、
   セクションの外を読ませない。
   エラーメッセージには、エラーを検出した位置(ファイルの先頭からのバイト数)を付ける。

   LEB128 の最長のエンコーディングは、`u32` と `i32` が 5 バイト、`i64` が 10 バイトである。
   最長のエンコーディングの最後のバイトは、継続ビットが立っていてはならない。
   そのバイトのうち値に使わないビットは、uLEB128 では 0 でなければならず、
   sLEB128 では値の符号ビットと同じでなければならない。
   値を変えない 0x80 や 0xFF のバイトを追加した冗長なエンコーディングも、
   この規則を満たせば受理する。 *)
exception Malformed of int * string

type rd = { src : string; mutable pos : int; mutable stop : int }

let fail r msg = raise (Malformed (r.pos, msg))

let get_u8 r =
  if r.pos >= r.stop then fail r "セクションの終わりを越えて読もうとしました";
  let c = Char.code r.src.[r.pos] in
  r.pos <- r.pos + 1;
  c

let get_uleb r =
  let rec go acc shift i =
    let byte = get_u8 r in
    if i = 4 && byte land 0xf0 <> 0 then fail r "uLEB128 が u32 の範囲を超えます";
    let acc = acc lor ((byte land 0x7f) lsl shift) in
    if byte land 0x80 = 0 then acc else go acc (shift + 7) (i + 1)
  in
  go 0 0 0

let get_sleb32 r =
  let rec go acc shift i =
    let byte = get_u8 r in
    if i = 4 && byte land 0x80 <> 0 then fail r "sLEB128 が長すぎます";
    if i = 4 && byte land 0x70 <> (if byte land 0x08 <> 0 then 0x70 else 0) then fail r "sLEB128 が i32 の範囲を超えます";
    let acc = acc lor ((byte land 0x7f) lsl shift) in
    let shift = shift + 7 in
    if byte land 0x80 <> 0 then go acc shift (i + 1) else if byte land 0x40 <> 0 then acc lor (-1 lsl shift) else acc
  in
  Int32.of_int (go 0 0 0)

let get_sleb64 r =
  let rec go acc shift i =
    let byte = get_u8 r in
    if i = 9 && byte <> 0 && byte <> 0x7f then fail r "sLEB128 が i64 の範囲を超えます";
    let acc = Int64.logor acc (Int64.shift_left (Int64.of_int (byte land 0x7f)) shift) in
    let shift = shift + 7 in
    if byte land 0x80 <> 0 then go acc shift (i + 1)
    else if byte land 0x40 <> 0 && shift < 64 then Int64.logor acc (Int64.shift_left (-1L) shift)
    else acc
  in
  go 0L 0 0

let get_f64 r =
  let bits = ref 0L in
  for i = 0 to 7 do
    bits := Int64.logor !bits (Int64.shift_left (Int64.of_int (get_u8 r)) (8 * i))
  done;
  !bits

let get_bytes r =
  let n = get_uleb r in
  if n > r.stop - r.pos then fail r "バイト列の長さがセクションの残りを超えます";
  let s = String.sub r.src r.pos n in
  r.pos <- r.pos + n;
  s

(* 個数は、セクションの残りのバイト数を超えてはならない。
   どの項目も 1 バイト以上を占めるので、残りのバイト数を超える個数はエラーである。
   先に検査しておくと、壊れた個数に従って大きな配列を作ろうとすることがない。 *)
let get_count r =
  let n = get_uleb r in
  if n > r.stop - r.pos then fail r "個数がセクションの残りのバイト数を超えます";
  n

(* 項目は先頭から順に読む。
   項目の個数だけ `f` を呼び、結果を逆順にためてから反転する。 *)
let get_list r f =
  let n = get_count r in
  let rec go acc i = if i = n then List.rev acc else go (f () :: acc) (i + 1) in
  go [] 0

let get_bool r what = match get_u8 r with 0 -> false | 1 -> true | _ -> fail r (what ^ "の値が 0 でも 1 でもありません")

let get_enum r what tbl =
  let c = get_u8 r in
  if c >= Array.length tbl then fail r (Printf.sprintf "%sの番号 %d は定義されていません" what c);
  tbl.(c)

let get_flags r what mask =
  let c = get_u8 r in
  if c land lnot mask <> 0 then fail r (what ^ "の印に定義されていないビットがあります");
  c

(* ## 20.9 表の参照

   リーダは、表を配列に読み込み、参照の添字が範囲内であることを検査してから項目を取り出す。
   strings と blobs の表は、項目が厳密な昇順に並び、
   どの項目も 1 回以上参照されていなければならない。
   prims の表も同じで、どの項目も `extern` のグローバルから参照されていなければならない。
   この規則により、テキストから作る表とバイナリの表が 1 対 1 に対応する。
   参照されたかどうかは、参照を読むたびにフラグを立てて記録する。
   prims の表は globals のセクションを読み終えた時点で検査し、
   strings と blobs の表はすべてのセクションを読み終えた後に検査する。 *)
type tables = {
  strs : string array;
  str_used : bool array;
  blobs : string array;
  blob_used : bool array;
  mutable t_types : ty array;
  mutable t_effects : eff array;
  mutable t_classes : cls array;
  mutable t_instances : string array;
  mutable t_prims : (abi * string) array;
  prim_used : bool array ref;
  mutable t_globals : string array;
  mutable t_fns : string array;
}

let idx r what n i = if i >= n then fail r (Printf.sprintf "%sの添字 %d が範囲外です(表のサイズは %d)" what i n) else i

let get_str r t =
  let i = idx r "strings" (Array.length t.strs) (get_uleb r) in
  t.str_used.(i) <- true;
  t.strs.(i)

let get_blob r t =
  let i = idx r "blobs" (Array.length t.blobs) (get_uleb r) in
  t.blob_used.(i) <- true;
  t.blobs.(i)

let get_ref r what arr = arr.(idx r what (Array.length arr) (get_uleb r))

let get_ty r t = get_ref r "型" t.t_types

let get_eff r t = get_ref r "エフェクト" t.t_effects

let get_cls r t = get_ref r "クラス" t.t_classes

let get_ctor r ty = (get_ref r "コンストラクタ" (Array.of_list ty.t_ctors)).ct_name

let get_op r ef = (get_ref r "操作" (Array.of_list ef.e_ops)).o_name

let get_meth r c = fst (get_ref r "メソッド" (Array.of_list c.c_methods))

let get_fn r t = get_ref r "関数" t.t_fns

let get_glob r t = get_ref r "グローバル" t.t_globals

let get_inst r t = get_ref r "インスタンス" t.t_instances

let get_rep r = get_enum r "Rep" rep_of_code

(* ## 20.10 式、辞書、パターンの読み込み

   木の深さは、引数 `d` で数える。
   深さが入れ子の上限を超えたら、OCaml のスタックオーバーフローに頼らず、その時点で拒否する。 *)
let nest r limit d = if d > limit then fail r "処理系の限度: KIR の読み込みで入れ子が深すぎます"

let get_lit r t =
  match get_u8 r with
  | 0 -> LBool false
  | 1 -> LBool true
  | 2 -> LI32 (get_sleb32 r)
  | 3 -> LI64 (get_sleb64 r)
  | 4 -> LF64 (get_f64 r)
  | 5 -> LStr (get_blob r t)
  | c -> fail r (Printf.sprintf "リテラルの種類 %d は定義されていません" c)

let get_var r =
  match get_u8 r with
  | 0 -> VLocal (get_uleb r)
  | 1 -> VEnv (get_uleb r)
  | 2 -> VDParam (get_uleb r)
  | c -> fail r (Printf.sprintf "キャプチャの種類 %d は定義されていません" c)

let rec get_dict r t lim d =
  nest r lim d;
  let sub () = get_dict r t lim (d + 1) in
  let fields () =
    get_list r (fun () ->
        let l = get_str r t in
        (l, sub ()))
  in
  match get_u8 r with
  | 0 ->
      let i = get_inst r t in
      DInst (i, get_list r sub)
  | 1 -> DVar (VDParam (get_uleb r))
  | 2 -> DVar (VEnv (get_uleb r))
  | 3 -> DRecord (fields ())
  | 4 -> DVariant (fields ())
  | 5 ->
      let c = get_cls r t in
      let ty = get_ty r t in
      DBuiltin (c.c_sym, ty.t_sym)
  | c -> fail r (Printf.sprintf "辞書の式の番号 %d は定義されていません" c)

let rec get_pat r t lim d =
  nest r lim d;
  let sub () = get_pat r t lim (d + 1) in
  match get_u8 r with
  | 0 -> PWild
  | 1 -> PBind (get_uleb r)
  | 2 -> PLit (get_lit r t)
  | 3 ->
      let tail = get_u8 r in
      if tail > 2 then fail r (Printf.sprintf "レコードのパターンの末尾の種類 %d は定義されていません" tail);
      let fs =
        get_list r (fun () ->
            let l = get_str r t in
            (l, sub ()))
      in
      let tl = match tail with 0 -> Closed | 1 -> Open | _ -> Rest (sub ()) in
      PRecord (fs, tl)
  | 4 ->
      let ty = get_ty r t in
      let c = get_ctor r ty in
      let fs =
        get_list r (fun () ->
            let i = get_uleb r in
            (i, sub ()))
      in
      PCtor (ty.t_sym, c, fs)
  | 5 ->
      let l = get_str r t in
      PVariant (l, sub ())
  | c -> fail r (Printf.sprintf "パターンの番号 %d は定義されていません" c)

let get_part r t =
  let f = get_fn r t in
  { p_fn = f; p_caps = get_list r (fun () -> get_var r) }

(* 子の個数を先に読む構文では、その個数だけ子を読む。
   OCaml は関数の引数を評価する順序を定めていないので、子を読む順序は `let` で固定する。 *)
let rec get_exp r t lim d =
  nest r lim d;
  let sub () = get_exp r t lim (d + 1) in
  let dict () = get_dict r t lim (d + 1) in
  let n_times n f =
    let rec go acc i = if i = n then List.rev acc else go (f () :: acc) (i + 1) in
    go [] 0
  in
  let count () = get_count r in
  match get_u8 r with
  | 0x00 -> Lit (get_lit r t)
  | 0x01 ->
      if get_u8 r <> 0 then fail r "範囲外のリテラルの種類が定義されていません";
      Lit_error (Lit_range, get_str r t)
  | 0x02 -> Local (get_uleb r)
  | 0x03 -> Env (get_uleb r)
  | 0x04 -> Global (get_glob r t)
  | 0x05 ->
      let ty = get_ty r t in
      let c = get_ctor r ty in
      let fs =
        get_list r (fun () ->
            let i = get_uleb r in
            (i, sub ()))
      in
      Construct (ty.t_sym, c, fs)
  | 0x06 ->
      let l = get_str r t in
      Variant (l, sub ())
  | 0x07 ->
      let flags = get_flags r "呼び出し" 3 in
      let n = count () in
      let f = sub () in
      let args = n_times n sub in
      Call { c_tail = flags land 1 <> 0; c_yield = flags land 2 <> 0; c_fn = f; c_args = args }
  | (0x08 | 0x09) as op ->
      let c = get_cls r t in
      let m = get_meth r c in
      let n = count () in
      let dd = dict () in
      if op = 0x08 then Method (c.c_sym, m, dd, n_times n dict) else Opcall (c.c_sym, m, dd, n_times n sub)
  | 0x0A -> Not (sub ())
  | 0x0B ->
      let a = sub () in
      And (a, sub ())
  | 0x0C ->
      let a = sub () in
      Or (a, sub ())
  | 0x0D ->
      let p = get_part r t in
      Closure (p.p_fn, p.p_caps)
  | 0x0E ->
      let p = get_part r t in
      Dictabs (p.p_fn, p.p_caps)
  | 0x0F ->
      let n = count () in
      let x = sub () in
      Dictapp (x, n_times n dict)
  | 0x10 ->
      let i = get_uleb r in
      let a = sub () in
      Let (i, a, sub ())
  | 0x11 ->
      let p = get_pat r t lim (d + 1) in
      let a = sub () in
      Letpat (p, a, sub ())
  | 0x12 ->
      let items =
        get_list r (fun () ->
            let i = get_uleb r in
            (i, sub ()))
      in
      if items = [] then fail r "letrec の項目がありません";
      Letrec (items, sub ())
  | 0x13 ->
      let xs = get_list r sub in
      if List.length xs < 2 then fail r "seq の要素が 2 個より少なくなっています";
      Seq xs
  | 0x14 ->
      let n = count () in
      let x = sub () in
      let cls =
        n_times n (fun () ->
            let g = get_bool r "ガードの有無" in
            let p = get_pat r t lim (d + 1) in
            let guard = if g then Some (sub ()) else None in
            { cl_pat = p; cl_guard = guard; cl_body = sub () })
      in
      Match (x, cls)
  | 0x15 -> Rec_empty
  | 0x16 ->
      let l = get_str r t in
      let v = sub () in
      Rec_extend (l, v, sub ())
  | 0x17 ->
      let l = get_str r t in
      Rec_select (l, sub ())
  | 0x18 ->
      let l = get_str r t in
      Rec_restrict (l, sub ())
  | 0x19 ->
      let l = get_str r t in
      let x = sub () in
      Rec_update (l, x, sub ())
  | 0x1A ->
      let ef = get_eff r t in
      let op = get_op r ef in
      Perform (ef.e_sym, op, get_list r sub)
  | 0x1B ->
      let flags = get_flags r "ハンドラ式" 7 in
      let ef = get_eff r t in
      let n = count () in
      if n = 0 then fail r "ハンドラ式の操作節がありません";
      let body = get_part r t in
      let ops =
        n_times n (fun () ->
            let op = get_op r ef in
            let cls = get_enum r "操作節の分類" class_of_code in
            (op, cls, get_part r t))
      in
      let ret = if flags land 2 <> 0 then Some (get_part r t) else None in
      let cancel = if flags land 4 <> 0 then Some (get_part r t) else None in
      Handle { h_tail = flags land 1 <> 0; h_effect = ef.e_sym; h_body = body; h_ops = ops; h_return = ret; h_cancel = cancel }
  | 0x1C ->
      let tl = get_bool r "resume の末尾の印" in
      Resume (tl, sub ())
  | 0x1D -> Hole
  | c -> fail r (Printf.sprintf "式の番号 0x%02x は定義されていません" c)

(* ## 20.11 セクションの読み込み *)
let get_fn_entry r t lim sym =
  let kind = get_enum r "関数の種類" kind_of_code in
  let yld = get_bool r "yield の印" in
  let params = get_list r (fun () -> get_rep r) in
  let locals = get_list r (fun () -> get_rep r) in
  let dicts = get_uleb r in
  let caps = get_list r (fun () -> get_rep r) in
  let result = get_rep r in
  let pats, guard =
    if kind = Opclause then (
      let pats = get_list r (fun () -> get_pat r t lim 1) in
      let g = get_bool r "ガードの有無" in
      (pats, if g then Some (get_exp r t lim 1) else None))
    else ([], None)
  in
  let body = get_exp r t lim 1 in
  { f_sym = sym; f_kind = kind; f_yield = yld; f_params = params; f_locals = locals; f_dicts = dicts; f_caps = caps; f_result = result; f_pats = pats; f_guard = guard; f_body = body }

let get_step r t lim =
  let globs () = get_list r (fun () -> get_glob r t) in
  match get_u8 r with
  | 0 ->
      let g = get_glob r t in
      Def_value (g, get_fn r t)
  | 1 ->
      let f = get_fn r t in
      let gs = globs () in
      Def_pattern (f, gs, get_pat r t lim 1)
  | 2 ->
      let gs = globs () in
      if gs = [] then fail r "def_fns のグローバルがありません";
      Def_fns gs
  | 3 -> Def_dictabs (get_glob r t)
  | 4 -> Def_instance (get_inst r t)
  | 5 -> Run_exp (get_fn r t)
  | c -> fail r (Printf.sprintf "初期化手順の番号 %d は定義されていません" c)

(* 表の項目が厳密な昇順に並んでいることを検査する。重複もエラーである *)
let check_sorted r what arr =
  for i = 1 to Array.length arr - 1 do
    if compare arr.(i - 1) arr.(i) >= 0 then fail r (what ^ "の表が厳密な昇順に並んでいません")
  done

(* ## 20.12 ファイルの読み込み

   読み込みは 3 段階で進む。

   1. ヘッダを検査し、各セクションの範囲を記録する。
      バージョンはメジャーバージョンだけを比べ、マイナーバージョンは問わない。
      必須機能ビットは 1 つも定義していないので、0 でなければ拒否する。
      セクションの id は厳密な昇順でなければならず、
      必須の 11 個のセクションがすべてそろっていなければならない。
      id が 0x00 のセクションと 0x0C から 0x7F のセクションは定義されていないので拒否し、
      0x80 以上のセクションはスキップする。
      最後のセクションの後ろにバイトが残っていてはならない。
      ヘッダに書かれたセクションの個数は、ファイルにあるセクションの個数と同じでなければならない。
   2. strings と blobs の表を読み、続いて関数のシンボルの並びを読む。
      ほかのセクションが関数を添字で指すので、シンボルの並びはそれらのセクションより先に読む。
   3. 残りのセクションを id の順に読む。
      各セクションは内容をちょうど読み終えなければならない。 *)
let decode_exn ~max_nest:lim src =
  let len = String.length src in
  let r = { src; pos = 0; stop = len } in
  if len < 16 then fail r "ヘッダの 16 バイトがありません";
  if String.sub src 0 4 <> magic then fail r "マジックナンバーが KIR のものではありません";
  r.pos <- 4;
  let u16 () =
    let a = get_u8 r in
    a lor (get_u8 r lsl 8)
  in
  let u32 () =
    let a = u16 () in
    a lor (u16 () lsl 16)
  in
  let major = u16 () in
  let minor = u16 () in
  if major <> fst Ir.version then
    fail r (Printf.sprintf "バージョン %d.%d は読めません(読めるのはメジャーバージョン %d のバージョンだけです)" major minor (fst Ir.version));
  let features = u32 () in
  if features <> 0 then fail r (Printf.sprintf "必須機能ビット 0x%08x を処理できません" features);
  let nsec = u32 () in
  let secs = Hashtbl.create 16 in
  let seen = ref 0 and last = ref 0 in
  while r.pos < len do
    let id = get_u8 r in
    if id = 0 || (id > sec_init && id < 0x80) then fail r (Printf.sprintf "セクション 0x%02x は定義されていません" id);
    if id <= !last then fail r (Printf.sprintf "セクション 0x%02x が id の昇順に並んでいません" id);
    last := id;
    let size = get_uleb r in
    if size > len - r.pos then fail r (Printf.sprintf "セクション 0x%02x のサイズがファイルの残りを超えます" id);
    Hashtbl.replace secs id (r.pos, r.pos + size);
    r.pos <- r.pos + size;
    incr seen
  done;
  if !seen <> nsec then fail r (Printf.sprintf "セクションの数がヘッダ(%d)と違います(%d)" nsec !seen);
  for id = sec_strings to sec_init do
    if not (Hashtbl.mem secs id) then fail r (Printf.sprintf "必須のセクション 0x%02x がありません" id)
  done;
  let enter id =
    let a, b = Hashtbl.find secs id in
    r.pos <- a;
    r.stop <- b
  in
  let leave id = if r.pos <> r.stop then fail r (Printf.sprintf "セクション 0x%02x の内容の後ろにバイトが残っています" id) in
  let in_section id f =
    enter id;
    let v = f () in
    leave id;
    v
  in
  let byte_table id what =
    in_section id (fun () ->
        let a = Array.of_list (get_list r (fun () -> get_bytes r)) in
        check_sorted r what a;
        a)
  in
  let strs = byte_table sec_strings "strings" in
  Array.iter (fun s -> if not (String.is_valid_utf_8 s) then fail r "strings の表に UTF-8 でない名前があります") strs;
  let blobs = byte_table sec_blobs "blobs" in
  let t =
    {
      strs;
      str_used = Array.make (Array.length strs) false;
      blobs;
      blob_used = Array.make (Array.length blobs) false;
      t_types = [||];
      t_effects = [||];
      t_classes = [||];
      t_instances = [||];
      t_prims = [||];
      prim_used = ref [||];
      t_globals = [||];
      t_fns = [||];
    }
  in
  (* 関数のシンボルの並びを読む。関数の項目は、後で同じセクションの続きから読む *)
  enter sec_functions;
  let nfn = get_count r in
  let rec syms acc i = if i = nfn then List.rev acc else syms (get_str r t :: acc) (i + 1) in
  t.t_fns <- Array.of_list (syms [] 0);
  let fn_items_pos = r.pos in
  let units =
    in_section sec_units (fun () ->
        get_list r (fun () ->
            let k = get_str r t in
            (k, get_list r (fun () -> get_blob r t))))
  in
  let types =
    in_section sec_types (fun () ->
        get_list r (fun () ->
            let s = get_str r t in
            let cs =
              get_list r (fun () ->
                  let n = get_str r t in
                  { ct_name = n; ct_arity = get_uleb r })
            in
            { t_sym = s; t_ctors = cs }))
  in
  t.t_types <- Array.of_list types;
  let effects =
    in_section sec_effects (fun () ->
        get_list r (fun () ->
            let s = get_str r t in
            let ops =
              get_list r (fun () ->
                  let n = get_str r t in
                  let a = get_uleb r in
                  let fl = get_flags r "操作" 3 in
                  { o_name = n; o_arity = a; o_never = fl land 1 <> 0; o_runtime = fl land 2 <> 0 })
            in
            { e_sym = s; e_ops = ops }))
  in
  t.t_effects <- Array.of_list effects;
  let classes =
    in_section sec_classes (fun () ->
        get_list r (fun () ->
            let s = get_str r t in
            let ms =
              get_list r (fun () ->
                  let n = get_str r t in
                  (n, get_uleb r))
            in
            { c_sym = s; c_methods = ms }))
  in
  t.t_classes <- Array.of_list classes;
  (* インスタンスのシンボルの並びは、先に読んでおく必要がない。インスタンスを指すのは後ろのセクションだけである *)
  let instances =
    in_section sec_instances (fun () ->
        get_list r (fun () ->
            let s = get_str r t in
            let c = get_cls r t in
            let h = get_ty r t in
            let n = get_uleb r in
            let ms =
              get_list r (fun () ->
                  let m = get_meth r c in
                  let k = get_uleb r in
                  (m, k, get_fn r t))
            in
            { i_sym = s; i_class = c.c_sym; i_head = h.t_sym; i_premises = n; i_methods = ms }))
  in
  t.t_instances <- Array.of_list (List.map (fun i -> i.i_sym) instances);
  let prims =
    in_section sec_prims (fun () ->
        Array.of_list
          (get_list r (fun () ->
               let a = get_enum r "ABI" abi_of_code in
               (a, get_str r t))))
  in
  check_sorted r "prims" (Array.map (fun (a, s) -> (abi_code a, s)) prims);
  t.t_prims <- prims;
  t.prim_used := Array.make (Array.length prims) false;
  let globals =
    in_section sec_globals (fun () ->
        get_list r (fun () ->
            let s = get_str r t in
            let kind =
              match get_u8 r with
              | 0 -> GBuiltin
              | 1 ->
                  let i = idx r "prims" (Array.length prims) (get_uleb r) in
                  !(t.prim_used).(i) <- true;
                  let abi, impl = prims.(i) in
                  GExtern { abi; impl; dicts = get_uleb r }
              | 2 -> GFn (get_fn r t)
              | 3 -> GDictabs (get_fn r t)
              | 4 -> GValue (get_rep r)
              | c -> fail r (Printf.sprintf "グローバルの種類 %d は定義されていません" c)
            in
            { g_sym = s; g_kind = kind }))
  in
  Array.iteri (fun i u -> if not u then fail r (Printf.sprintf "prims の項目 %d を参照する extern のグローバルがありません" i)) !(t.prim_used);
  t.t_globals <- Array.of_list (List.map (fun g -> g.g_sym) globals);
  enter sec_functions;
  r.pos <- fn_items_pos;
  let functions = Array.to_list (Array.map (fun sym -> get_fn_entry r t lim sym) t.t_fns) in
  leave sec_functions;
  let inits = in_section sec_init (fun () -> get_list r (fun () -> get_list r (fun () -> get_step r t lim))) in
  if List.length inits <> List.length units then fail r "init のセクションの単位の数が units のセクションと違います";
  Array.iteri (fun i u -> if not u then fail r (Printf.sprintf "strings の項目 %d がどこからも使われていません" i)) t.str_used;
  Array.iteri (fun i u -> if not u then fail r (Printf.sprintf "blobs の項目 %d がどこからも使われていません" i)) t.blob_used;
  let units = List.map2 (fun (k, ps) steps -> { u_key = k; u_paths = ps; u_init = steps }) units inits in
  { version = (major, minor); units; types; effects; classes; instances; globals; functions }

(* 読み込みのエントリポイントである。
   壊れたファイルを読んだときに起こる例外は、すべてエラーメッセージに変える。
   入れ子の上限で深さを抑えているので、
   `Stack_overflow` は、上限の深さに必要なスタックより小さいスタックでだけ起こる。 *)
let decode ?(max_nest = max_nest) src =
  match decode_exn ~max_nest src with
  | p -> Ok p
  | exception Malformed (pos, msg) -> Error (Printf.sprintf "位置 %d: %s" pos msg)
  | exception Stack_overflow -> Error "処理系の限度: KIR の読み込みでスタックオーバーフローになりました"
  | exception Out_of_memory -> Error "KIR の読み込みでメモリが不足しました"
  | exception (Invalid_argument _ | Not_found) -> Error "KIR の読み込みで表の参照を解決できません"
