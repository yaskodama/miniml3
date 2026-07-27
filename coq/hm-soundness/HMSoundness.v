From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

(*
  A small Coq development for Hindley-Milner style type inference soundness.

  Scope:
    - Terms: variables, integer literals, lambda, application, let.
    - Types: int, variables, arrows.
    - Schemes: either monomorphic, or an abstract forall wrapper.
    - Instantiation and generalization are kept as relations.  This keeps the
      proof focused on the soundness shape of HM inference, not on a particular
      implementation of free-variable sets and substitution.

  The central theorem is [hm_infer_sound]:

      if the HM inference judgement infers type [T] for expression [e],
      then [e] is well typed with [T] in the declarative HM system.
*)

Inductive ty : Type :=
| TInt : ty
| TVar : nat -> ty
| TArrow : ty -> ty -> ty.

Inductive expr : Type :=
| EVar : nat -> expr
| EInt : nat -> expr
| ELam : nat -> expr -> expr
| EApp : expr -> expr -> expr
| ELet : nat -> expr -> expr -> expr.

Inductive scheme : Type :=
| Mono : ty -> scheme
| Forall : list nat -> ty -> scheme.

Definition env := nat -> option scheme.

Definition empty : env := fun _ => None.

Definition extend (G : env) (x : nat) (s : scheme) : env :=
  fun y => if Nat.eqb x y then Some s else G y.

Inductive inst : scheme -> ty -> Prop :=
| InstMono :
    forall T,
      inst (Mono T) T
| InstForallSame :
    forall xs T,
      inst (Forall xs T) T.

Inductive gen : env -> ty -> scheme -> Prop :=
| GenMono :
    forall G T,
      gen G T (Mono T)
| GenForall :
    forall G xs T,
      gen G T (Forall xs T).

Inductive has_type : env -> expr -> ty -> Prop :=
| TyVar :
    forall G x s T,
      G x = Some s ->
      inst s T ->
      has_type G (EVar x) T
| TyInt :
    forall G n,
      has_type G (EInt n) TInt
| TyLam :
    forall G x body TArg TBody,
      has_type (extend G x (Mono TArg)) body TBody ->
      has_type G (ELam x body) (TArrow TArg TBody)
| TyApp :
    forall G f a TArg TRes,
      has_type G f (TArrow TArg TRes) ->
      has_type G a TArg ->
      has_type G (EApp f a) TRes
| TyLet :
    forall G x e1 e2 T1 S T2,
      has_type G e1 T1 ->
      gen G T1 S ->
      has_type (extend G x S) e2 T2 ->
      has_type G (ELet x e1 e2) T2.

(*
  Algorithmic HM inference as a relation.

  Read [hm_infer G e T] as: the inference procedure can infer [T] for [e].
  The application rule corresponds to the successful post-unification shape:
  the function has an arrow type whose argument matches the inferred argument.
*)
Inductive hm_infer : env -> expr -> ty -> Prop :=
| InfVar :
    forall G x s T,
      G x = Some s ->
      inst s T ->
      hm_infer G (EVar x) T
| InfInt :
    forall G n,
      hm_infer G (EInt n) TInt
| InfLam :
    forall G x body TArg TBody,
      hm_infer (extend G x (Mono TArg)) body TBody ->
      hm_infer G (ELam x body) (TArrow TArg TBody)
| InfApp :
    forall G f a TArg TRes,
      hm_infer G f (TArrow TArg TRes) ->
      hm_infer G a TArg ->
      hm_infer G (EApp f a) TRes
| InfLet :
    forall G x e1 e2 T1 S T2,
      hm_infer G e1 T1 ->
      gen G T1 S ->
      hm_infer (extend G x S) e2 T2 ->
      hm_infer G (ELet x e1 e2) T2.

Theorem hm_infer_sound :
  forall G e T,
    hm_infer G e T ->
    has_type G e T.
Proof.
  intros G e T H.
  induction H.
  - eapply TyVar; eauto.
  - constructor.
  - apply TyLam. exact IHhm_infer.
  - eapply TyApp; eauto.
  - eapply TyLet; eauto.
Qed.

(*
  A concrete sample:

      let id = fun x -> x in id 42

  The proof below derives its type through the inference judgement, then uses
  [hm_infer_sound] to obtain the declarative typing theorem.
*)

Definition id_body : expr := ELam 0 (EVar 0).
Definition id_program : expr := ELet 1 id_body (EApp (EVar 1) (EInt 42)).

Lemma infer_id_program :
  hm_infer empty id_program TInt.
Proof.
  unfold id_program, id_body.
  eapply InfLet with (T1 := TArrow TInt TInt) (S := Forall [0] (TArrow TInt TInt)).
  - apply InfLam.
    eapply InfVar.
    + unfold extend. now rewrite Nat.eqb_refl.
    + constructor.
  - constructor.
  - eapply InfApp with (TArg := TInt).
    + eapply InfVar.
      * unfold extend. now rewrite Nat.eqb_refl.
      * constructor.
    + constructor.
Qed.

Theorem id_program_sound :
  has_type empty id_program TInt.
Proof.
  apply hm_infer_sound.
  exact infer_id_program.
Qed.

(*
  Another sample:

      fun x -> x + 1

  We model [+] as a variable in the environment with type int -> int -> int.
*)

Definition plus_ty : ty := TArrow TInt (TArrow TInt TInt).
Definition plus_env : env := extend empty 10 (Mono plus_ty).
Definition inc_expr : expr :=
  ELam 0 (EApp (EApp (EVar 10) (EVar 0)) (EInt 1)).

Lemma infer_inc_expr :
  hm_infer plus_env inc_expr (TArrow TInt TInt).
Proof.
  unfold inc_expr, plus_env, plus_ty.
  apply InfLam.
  eapply InfApp with (TArg := TInt).
  - eapply InfApp with (TArg := TInt).
    + eapply InfVar.
      * unfold extend.
        destruct (Nat.eqb 0 10) eqn:E.
        -- apply Nat.eqb_eq in E. discriminate E.
        -- now rewrite Nat.eqb_refl.
      * constructor.
    + eapply InfVar.
      * unfold extend. now rewrite Nat.eqb_refl.
      * constructor.
  - constructor.
Qed.

Theorem inc_expr_sound :
  has_type plus_env inc_expr (TArrow TInt TInt).
Proof.
  apply hm_infer_sound.
  exact infer_inc_expr.
Qed.
