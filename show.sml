(* ================================================================
   show.sml -- 値と型の表示。出力の書式は miniml2 と同一。
   ================================================================ *)
structure Show =
struct
  open Value
  open Types

  fun escape s = "\"" ^ String.toString s ^ "\""

  fun showValue v =
      case v of
          Val_number n => Absyn.intToString n
        | Val_bool b   => Bool.toString b
        | Val_string s => escape s
        | Val_unit     => "()"
        | Val_nil      => "[]"
        | Val_pair (a, b) => "(" ^ showValue a ^ ", " ^ showValue b ^ ")"
        | Val_cons _   => "[" ^ showList v ^ "]"
        | Val_closure _ => "<fun>"
        | Val_primitive _ => "<fun>"

  and showList (Val_cons (h, t)) =
        (case t of
             Val_nil => showValue h
           | Val_cons _ => showValue h ^ "; " ^ showList t
           | _ => showValue h ^ "; " ^ showValue t)
    | showList v = showValue v

  val name_of_variables = ref ([] : (tyvar * string) list)
  val count_of_variables = ref 0

  fun var_name vv =
      Util.assoc vv (!name_of_variables)
      handle Util.Not_found =>
        let val n = !count_of_variables
            val name = if n < 26
                       then "'" ^ String.str (Char.chr (Char.ord #"a" + n))
                       else "'t" ^ Int.toString n
        in count_of_variables := n + 1;
           name_of_variables := (vv, name) :: !name_of_variables;
           name
        end

  fun showType ty =
      case shorten ty of
          VarType vv => var_name vv
        | Term (c, []) => c
        | Term (c, [t]) => showType t ^ " " ^ c
        | Term (c, [t1, t2]) =>
            "(" ^ showType t1 ^ " " ^ c ^ " " ^ showType t2 ^ ")"
        | Term (c, args) =>
            "(" ^ String.concatWith ", " (List.map showType args) ^ ") " ^ c

  fun showTypeTop ty =
      (name_of_variables := []; count_of_variables := 0; showType ty)

  fun showSchema ({ parameters, bodys } : schema) =
      (name_of_variables := []; count_of_variables := 0;
       (if null parameters then ""
        else "for all " ^ String.concatWith " " (List.map var_name parameters) ^ ", ")
       ^ showType bodys)
end
