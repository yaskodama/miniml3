(* ================================================================
   prims.sml -- 初期環境。miniml2 と同じ組み込み。
   ================================================================ *)
structure Prims =
struct
  open Value
  open Types

  fun prim_arith name f =
      Val_primitive (name,
        fn Val_pair (Val_number a, Val_number b) => Val_number (f (a, b))
         | _ => raise Eval_error (name ^ ": two integers expected"))

  fun prim_cmp name test =
      Val_primitive (name,
        fn Val_pair (a, b) => Val_bool (test (val_compare (a, b)))
         | _ => raise Eval_error (name ^ ": a pair expected"))

  fun safe_div name f =
      fn (a, b) => if IntInf.sign b = 0
                   then raise Eval_error "division by zero"
                   else f (a, b)

  val val_env_initial = [
      ("+",   prim_arith "+" IntInf.+),
      ("-",   prim_arith "-" IntInf.-),
      ("*",   prim_arith "*" IntInf.* ),
      ("/",   prim_arith "/" (safe_div "/" IntInf.div)),
      (* OCaml の mod は被除数の符号に従うので Int.rem 相当を使う *)
      ("mod", prim_arith "mod" (safe_div "mod" IntInf.rem)),
      ("=",   prim_cmp "="  (fn r => r = EQUAL)),
      ("<>",  prim_cmp "<>" (fn r => r <> EQUAL)),
      ("<",   prim_cmp "<"  (fn r => r = LESS)),
      (">",   prim_cmp ">"  (fn r => r = GREATER)),
      ("<=",  prim_cmp "<=" (fn r => r <> GREATER)),
      (">=",  prim_cmp ">=" (fn r => r <> LESS)),
      ("^",   Val_primitive ("^",
                fn Val_pair (Val_string a, Val_string b) => Val_string (a ^ b)
                 | _ => raise Eval_error "^: two strings expected")),
      ("not", Val_primitive ("not",
                fn Val_bool b => Val_bool (not b)
                 | _ => raise Eval_error "not: a boolean expected")),
      ("hd",  Val_primitive ("hd",
                fn Val_cons (h, _) => h
                 | _ => raise Eval_error "hd: empty list")),
      ("tl",  Val_primitive ("tl",
                fn Val_cons (_, t) => t
                 | _ => raise Eval_error "tl: empty list")),
      ("fst", Val_primitive ("fst",
                fn Val_pair (a, _) => a
                 | _ => raise Eval_error "fst: a pair expected")),
      ("snd", Val_primitive ("snd",
                fn Val_pair (_, b) => b
                 | _ => raise Eval_error "snd: a pair expected")),
      ("string_of_int", Val_primitive ("string_of_int",
                fn Val_number n => Val_string (Absyn.intToString n)
                 | _ => raise Eval_error "string_of_int: an integer expected")),
      ("print_string", Val_primitive ("print_string",
                fn Val_string s => (print s; Val_unit)
                 | _ => raise Eval_error "print_string: a string expected")),
      ("print_int", Val_primitive ("print_int",
                fn Val_number n => (print (Absyn.intToString n); Val_unit)
                 | _ => raise Eval_error "print_int: an integer expected")),
      ("print_newline", Val_primitive ("print_newline",
                fn _ => (print "\n"; Val_unit))),
      ("write_int", Val_primitive ("write_int",
                fn Val_number n => (print (Absyn.intToString n ^ "\n"); Val_number n)
                 | _ => raise Eval_error "write_int: an integer expected")),
      (* ---- 文字列を分解するための組み込み ---- *)
      ("size", Val_primitive ("size",
                fn Val_string s => Val_number (IntInf.fromInt (String.size s))
                 | _ => raise Eval_error "size: a string expected")),
      ("sub", Val_primitive ("sub",          (* sub s i : i 文字目の 1 文字 *)
                fn Val_string s => Val_primitive ("sub",
                     fn Val_number i =>
                          let val k = IntInf.toInt i handle Overflow => ~1
                          in if k < 0 orelse k >= String.size s
                             then raise Eval_error "sub: index out of range"
                             else Val_string (String.str (String.sub (s, k)))
                          end
                      | _ => raise Eval_error "sub: an integer expected")
                 | _ => raise Eval_error "sub: a string expected")),
      ("ord", Val_primitive ("ord",          (* 先頭 1 文字の文字コード *)
                fn Val_string s =>
                     if String.size s = 0 then raise Eval_error "ord: empty string"
                     else Val_number (IntInf.fromInt (Char.ord (String.sub (s, 0))))
                 | _ => raise Eval_error "ord: a string expected")),
      ("chr", Val_primitive ("chr",
                fn Val_number n =>
                     let val k = IntInf.toInt n handle Overflow => ~1
                     in if k < 0 orelse k > 255
                        then raise Eval_error "chr: out of range"
                        else Val_string (String.str (Char.chr k))
                     end
                 | _ => raise Eval_error "chr: an integer expected")),
      ("explode", Val_primitive ("explode",   (* 1 文字ずつの文字列のリストへ *)
                fn Val_string s =>
                     List.foldr (fn (c, acc) => Val_cons (Val_string (String.str c), acc))
                                Val_nil (String.explode s)
                 | _ => raise Eval_error "explode: a string expected")),
      ("implode", Val_primitive ("implode",
                fn v =>
                  let fun go Val_nil acc = String.concat (List.rev acc)
                        | go (Val_cons (Val_string s, t)) acc = go t (s :: acc)
                        | go _ _ = raise Eval_error "implode: a list of strings expected"
                  in Val_string (go v []) end)),
      ("quit", Val_primitive ("quit", fn _ => raise Util.End_of_system))
  ]

  val type_arithmetic =
      schema_trivial (type_arrow (type_product type_int type_int) type_int)
  val type_comparison =
      poly1 (fn a => type_arrow (type_product a a) type_bool)

  val type_env_initial = [
      ("+", type_arithmetic), ("-", type_arithmetic), ("*", type_arithmetic),
      ("/", type_arithmetic), ("mod", type_arithmetic),
      ("=", type_comparison), ("<>", type_comparison),
      ("<", type_comparison), (">", type_comparison),
      ("<=", type_comparison), (">=", type_comparison),
      ("^", schema_trivial
              (type_arrow (type_product type_string type_string) type_string)),
      ("not", schema_trivial (type_arrow type_bool type_bool)),
      ("hd",  poly1 (fn a => type_arrow (type_list a) a)),
      ("tl",  poly1 (fn a => type_arrow (type_list a) (type_list a))),
      ("fst", poly2 (fn a => fn b => type_arrow (type_product a b) a)),
      ("snd", poly2 (fn a => fn b => type_arrow (type_product a b) b)),
      ("string_of_int", schema_trivial (type_arrow type_int type_string)),
      ("print_string", schema_trivial (type_arrow type_string type_unit)),
      ("print_int", schema_trivial (type_arrow type_int type_unit)),
      ("print_newline", schema_trivial (type_arrow type_unit type_unit)),
      ("write_int", schema_trivial (type_arrow type_int type_int)),
      ("size", schema_trivial (type_arrow type_string type_int)),
      ("sub", schema_trivial (type_arrow type_string (type_arrow type_int type_string))),
      ("ord", schema_trivial (type_arrow type_string type_int)),
      ("chr", schema_trivial (type_arrow type_int type_string)),
      ("explode", schema_trivial (type_arrow type_string (type_list type_string))),
      ("implode", schema_trivial (type_arrow (type_list type_string) type_string)),
      ("quit", poly1 (fn a => type_arrow type_unit a))
  ]
end
