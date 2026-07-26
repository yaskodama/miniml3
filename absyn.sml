(* ================================================================
   absyn.sml -- 抽象構文。miniml2 と同一の構文木を作る。
   ================================================================ *)
structure Absyn =
struct

  (* object 言語の整数は多倍長 *)
  type num = IntInf.int

  datatype expr =
      Number      of num
    | Str         of string
    | Boolean     of bool
    | Variable    of string
    | Nil
    | Unit
    | Pair        of expr * expr
    | Cons        of expr * expr
    | If          of expr * expr * expr
    | Function    of (motif * expr) list
    | Application of expr * expr
    | Let         of bool * string * expr * expr   (* let [rec] x = e1 in e2 *)

  and motif =
      Motif_variable of string
    | Motif_wild
    | Motif_number  of num
    | Motif_string  of string
    | Motif_boolean of bool
    | Motif_unit
    | Motif_nil
    | Motif_pair of motif * motif
    | Motif_cons of motif * motif

  datatype definition =
      Def  of bool * string * expr                 (* let [rec] x = e *)
    | Expr of expr

  (* let f x y = e  は  let f = function x -> function y -> e  の略記 *)
  fun curry_fun [] body = body
    | curry_fun (p :: ps) body = Function [(p, curry_fun ps body)]

  (* 二項演算子は組を取る関数の適用として表す *)
  fun binop oper e1 e2 = Application (Variable oper, Pair (e1, e2))

  (* SML は負の整数を ~1 と書くが、この言語は Caml と同じく -1 *)
  fun intToString (n : num) =
      String.translate (fn #"~" => "-" | c => String.str c) (IntInf.toString n)

end

(* 連想リストの検索。値の環境と型の環境で共用する。 *)
structure Util =
struct
  exception Not_found
  exception End_of_system

  fun assoc x ((a, b) :: rest) = if x = a then b else assoc x rest
    | assoc _ [] = raise Not_found
end
