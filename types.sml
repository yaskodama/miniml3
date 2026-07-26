(* ================================================================
   types.sml -- Hindley/Milner の型推論。miniml2 と同じ。
   ================================================================ *)
structure Types =
struct
  open Absyn

  datatype simple_type =
      VarType of { index : int, value : tyval } ref
    | Term of string * simple_type list
  and tyval = Unknown | Known of simple_type

  type tyvar = { index : int, value : tyval } ref
  type schema = { parameters : tyvar list, bodys : simple_type }

  exception Type_error of string
  exception Circulation of simple_type * simple_type
  exception Conflict of simple_type * simple_type

  val type_int    = Term ("int", [])
  val type_bool   = Term ("bool", [])
  val type_string = Term ("string", [])
  val type_unit   = Term ("unit", [])
  fun type_arrow t1 t2   = Term ("->", [t1, t2])
  fun type_product t1 t2 = Term ("*",  [t1, t2])
  fun type_list t        = Term ("list", [t])

  fun schema_trivial ty : schema = { parameters = [], bodys = ty }

  (* 全称量化された型変数を一つ／二つ持つ型スキーム *)
  fun poly1 f : schema =
      let val a = ref { index = 0, value = Unknown }
      in { parameters = [a], bodys = f (VarType a) } end
  fun poly2 f : schema =
      let val a = ref { index = 0, value = Unknown }
          val b = ref { index = 0, value = Unknown }
      in { parameters = [a, b], bodys = f (VarType a) (VarType b) } end

  val level = ref 0
  fun start_of_definition () = level := !level + 1
  fun end_of_definition ()   = level := !level - 1
  fun new_unknown () = VarType (ref { index = !level, value = Unknown })

  fun shorten ty =
      case ty of
          VarType (vv as ref { index = i, value = Known t }) =>
            let val t' = shorten t
            in vv := { index = i, value = Known t' }; t' end
        | _ => ty

  fun gen ty : schema =
      let val parameters = ref ([] : tyvar list)
          fun find ty =
              case shorten ty of
                  VarType (vv as ref { index = i, value = _ }) =>
                    if i > !level andalso
                       not (List.exists (fn v => v = vv) (!parameters))
                    then parameters := vv :: !parameters
                    else ()
                | Term (_, args) => List.app find args
      in find ty; { parameters = !parameters, bodys = ty } end

  fun test_of_occurrence vv ty =
      let fun test t =
              case shorten t of
                  VarType vv1 => if vv1 = vv then raise Circulation (VarType vv, ty)
                                 else ()
                | Term (_, args) => List.app test args
      in test ty end

  fun modify_level lmax ty =
      case shorten ty of
          VarType (vv as ref { index = i, value = v }) =>
            if i > lmax then vv := { index = lmax, value = v } else ()
        | Term (_, args) => List.app (modify_level lmax) args

  fun unify (ty1, ty2) =
      let val v1 = shorten ty1
          val v2 = shorten ty2
      in
        if v1 = v2 then ()
        else
          case (v1, v2) of
              (VarType (vv as ref { index = i, value = _ }), ty) =>
                (test_of_occurrence vv ty; modify_level i ty;
                 vv := { index = i, value = Known ty })
            | (ty, VarType (vv as ref { index = i, value = _ })) =>
                (test_of_occurrence vv ty; modify_level i ty;
                 vv := { index = i, value = Known ty })
            | (Term (c1, a1), Term (c2, a2)) =>
                if c1 <> c2 orelse length a1 <> length a2
                then raise Conflict (v1, v2)
                else ListPair.app unify (a1, a2)
      end

  fun specialization ({ parameters = [], bodys } : schema) = bodys
    | specialization { parameters, bodys } =
        let val fresh = List.map (fn v => (v, new_unknown ())) parameters
            fun copy ty =
                case shorten ty of
                    (t as VarType v) => (Util.assoc v fresh handle Util.Not_found => t)
                  | Term (c, args) => Term (c, List.map copy args)
        in copy bodys end

  fun type_motif env m =
      case m of
          Motif_variable id =>
            let val ty = new_unknown ()
            in (ty, (id, schema_trivial ty) :: env) end
        | Motif_wild      => (new_unknown (), env)
        | Motif_boolean _ => (type_bool, env)
        | Motif_number _  => (type_int, env)
        | Motif_string _  => (type_string, env)
        | Motif_unit      => (type_unit, env)
        | Motif_nil       => (type_list (new_unknown ()), env)
        | Motif_pair (m1, m2) =>
            let val (t1, env1) = type_motif env m1
                val (t2, env2) = type_motif env1 m2
            in (type_product t1 t2, env2) end
        | Motif_cons (m1, m2) =>
            let val (t1, env1) = type_motif env m1
                val (t2, env2) = type_motif env1 m2
            in unify (type_list t1, t2); (t2, env2) end

  fun type_exp env e =
      case e of
          Number _  => type_int
        | Str _     => type_string
        | Boolean _ => type_bool
        | Unit      => type_unit
        | Nil       => type_list (new_unknown ())
        | Variable id =>
            (specialization (Util.assoc id env)
             handle Util.Not_found => raise Type_error (id ^ " is not bound"))
        | Pair (a, b) => type_product (type_exp env a) (type_exp env b)
        | Cons (a, b) =>
            let val ta = type_exp env a
                val tb = type_exp env b
            in unify (type_list ta, tb); tb end
        | If (c, a, b) =>
            let val tc = type_exp env c
                val ta = type_exp env a
                val tb = type_exp env b
            in unify (tc, type_bool); unify (ta, tb); ta end
        | Let (r, n, a, b) => type_exp (type_def env (r, n, a)) b
        | Function cases =>
            let val targ = new_unknown ()
                val tres = new_unknown ()
                fun case_type (m, body) =
                    let val (tm, env') = type_motif env m
                    in unify (tm, targ); unify (type_exp env' body, tres) end
            in List.app case_type cases; type_arrow targ tres end
        | Application (f, a) =>
            let val tf = type_exp env f
                val ta = type_exp env a
                val tr = new_unknown ()
            in unify (tf, type_arrow ta tr); tr end

  and type_def env (isrec, name, e) =
      (start_of_definition ();
       let val te =
               if isrec then
                   let val prov = new_unknown ()
                       val te = type_exp ((name, schema_trivial prov) :: env) e
                   in unify (te, prov); te end
               else type_exp env e
       in end_of_definition (); (name, gen te) :: env end)
end
