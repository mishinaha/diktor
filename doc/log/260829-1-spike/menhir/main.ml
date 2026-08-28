let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let () =
  let dump = Array.length Sys.argv > 2 && Sys.argv.(2) = "--dump" in
  let src = read_file Sys.argv.(1) in
  let toks = Lex.tokenize src in
  if dump then
    List.iter (fun (tk : Lex.tok) -> Printf.printf "%d %s\n" tk.line (Lex.show tk.t)) toks;
  let arr = Array.of_list toks in
  let idx = ref 0 in
  let last = ref 0 in
  let next (_ : Lexing.lexbuf) =
    if !idx >= Array.length arr then Kel.EOF
    else begin
      let (tk : Lex.tok) = arr.(!idx) in
      incr idx; last := tk.line; tk.t
    end
  in
  let lb = Lexing.from_string "" in
  (try
     Kel.program next lb;
     Printf.printf "OK: parsed %s (%d tokens)\n" Sys.argv.(1) (Array.length arr)
   with
   | Kel.Error ->
     let ctx =
       let lo = max 0 (!idx - 8) and hi = min (Array.length arr - 1) (!idx + 3) in
       String.concat " " (List.init (hi - lo + 1) (fun k -> Lex.show arr.(lo + k).Lex.t))
     in
     Printf.printf "PARSE ERROR near line %d (token #%d)\n  ... %s ...\n" !last !idx ctx;
     exit 1
   | Lex.Lex_error (m, l) -> Printf.printf "LEX ERROR line %d: %s\n" l m; exit 2)
