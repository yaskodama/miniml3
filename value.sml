(* ================================================================
   value.sml -- 値と評価器。miniml2 と同じ意味論。
   ================================================================ *)
structure Value =
struct
  open Absyn

  datatype value =
      Val_number    of num
    | Val_bool      of bool
    | Val_string    of string
    | Val_unit
    | Val_nil
    | Val_pair      of value * value
    | Val_cons      of value * value
    | Val_closure   of (motif * expr) list * (string * value) list ref
    | Val_primitive of string * (value -> value)

  exception Eval_error of string
  exception Fail_filtrate

  (* 構造的な順序。関数値は比較できない。 *)
  fun val_compare (v1, v2) =
      case (v1, v2) of
          (Val_number a, Val_number b) => IntInf.compare (a, b)
        | (Val_string a, Val_string b) => String.compare (a, b)
        | (Val_bool a, Val_bool b) =>
            if a = b then EQUAL else if b then LESS else GREATER
        | (Val_unit, Val_unit) => EQUAL
        | (Val_nil, Val_nil) => EQUAL
        | (Val_nil, Val_cons _) => LESS
        | (Val_cons _, Val_nil) => GREATER
        | (Val_pair (a, b), Val_pair (c, d)) =>
            (case val_compare (a, c) of EQUAL => val_compare (b, d) | r => r)
        | (Val_cons (a, b), Val_cons (c, d)) =>
            (case val_compare (a, c) of EQUAL => val_compare (b, d) | r => r)
        | _ => raise Eval_error "these values cannot be compared"

  fun filtrate (v, m) =
      case (v, m) of
          (_, Motif_variable id) => [(id, v)]
        | (_, Motif_wild) => []
        | (Val_bool a,   Motif_boolean b) => if a = b then [] else raise Fail_filtrate
        | (Val_number a, Motif_number b)  => if a = b then [] else raise Fail_filtrate
        | (Val_string a, Motif_string b)  => if a = b then [] else raise Fail_filtrate
        | (Val_unit, Motif_unit) => []
        | (Val_nil,  Motif_nil)  => []
        | (Val_pair (a, b), Motif_pair (m1, m2)) => filtrate (a, m1) @ filtrate (b, m2)
        | (Val_cons (a, b), Motif_cons (m1, m2)) => filtrate (a, m1) @ filtrate (b, m2)
        | _ => raise Fail_filtrate

  fun value_application env cases arg =
      case cases of
          [] => raise Eval_error "no matching case in this function"
        | ((m, body) :: rest) =>
            (let val env' = filtrate (arg, m) @ env
             in eval env' body end
             handle Fail_filtrate => value_application env rest arg)

  and value_definition env (isrec, name, e) =
      if isrec then
          case e of
              Function cases =>
                let val cell = ref []
                    val env' = (name, Val_closure (cases, cell)) :: env
                in cell := env'; env' end
            | _ => raise Eval_error ("`let rec " ^ name ^ "' must define a function")
      else (name, eval env e) :: env

  and eval env e =
      case e of
          Number n   => Val_number n
        | Str s      => Val_string s
        | Boolean b  => Val_bool b
        | Nil        => Val_nil
        | Unit       => Val_unit
        | Variable id =>
            (Util.assoc id env
             handle Util.Not_found => raise Eval_error (id ^ " is not bound"))
        | Pair (a, b) => Val_pair (eval env a, eval env b)
        | Cons (a, b) => Val_cons (eval env a, eval env b)
        | If (c, a, b) =>
            (case eval env c of
                 Val_bool true  => eval env a
               | Val_bool false => eval env b
               | _ => raise Eval_error "the condition of `if' is not a boolean")
        | Function cases => Val_closure (cases, ref env)
        | Let (r, n, a, b) => eval (value_definition env (r, n, a)) b
        | Application (f, a) =>
            let val vf = eval env f
                val va = eval env a
            in case vf of
                   Val_primitive (_, p) => p va
                 | Val_closure (cases, cell) => value_application (!cell) cases va
                 | _ => raise Eval_error "this value is not a function"
            end
end
