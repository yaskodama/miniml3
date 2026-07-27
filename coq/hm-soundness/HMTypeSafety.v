From Coq Require Import Bool.Bool Arith.PeanoNat Lists.List.
Import ListNotations.

(*
  Type safety for a polymorphic core language.

  What changed with respect to the first version of this file
  -----------------------------------------------------------
  The earlier development called itself Hindley-Milner but its types were

      Inductive ty := TInt | TArrow : ty -> ty -> ty.

  -- no type variables at all.  Lambdas carried an explicit annotation and
  [let] was monomorphic, so what was proved was the type safety of the simply
  typed lambda calculus with let and addition.  Nothing polymorphic occurred
  anywhere.

  Here types have variables, environments map to type schemes, and [let] is
  polymorphic: the bound expression is required to be typeable at every
  instance of the scheme, and each occurrence of the bound variable may pick a
  different instance.  Lambdas lost their annotation (Curry style), so the
  language is the untyped calculus typed by the relation, as in a real HM
  system.  [poly_program] below is a program that is typeable here and is not
  typeable in the monomorphic system, which is what makes the extension real
  rather than cosmetic.

  Quantified variables are de Bruijn indices ([TBound]) drawn from a
  constructor distinct from free variables ([TFree]).  Instantiation replaces
  only [TBound], and the types substituted in contain only [TFree], so variable
  capture cannot arise and no freshness side conditions are needed.  This is
  what keeps the development short enough to be checked end to end.

  Generalisation is given semantically: the [TyLet] rule asks that [e1] be
  typeable at every instance of the scheme, rather than computing the scheme
  from the free variables of the environment as HMSoundness.v does.  The two
  files therefore treat generalisation from the two standard angles: the
  syntactic side condition there, typeability at all instances here.
*)

(* ------------------------------------------------------------------ *)
(* Types and schemes                                                   *)
(* ------------------------------------------------------------------ *)

Inductive ty : Type :=
| TInt : ty
| TFree : nat -> ty          (* a free type variable *)
| TBound : nat -> ty         (* a variable bound by the enclosing scheme *)
| TArrow : ty -> ty -> ty.

(* [Sch n T] is  forall a_0 ... a_{n-1}. T,
   where a_i occurs in T as [TBound i]. *)
Inductive scheme : Type :=
| Sch : nat -> ty -> scheme.

Definition Mono (T : ty) : scheme := Sch 0 T.

(* Instantiation replaces the bound indices by the given types. *)
Fixpoint open (ts : list ty) (T : ty) : ty :=
  match T with
  | TInt => TInt
  | TFree a => TFree a
  | TBound i => nth i ts (TBound i)
  | TArrow A B => TArrow (open ts A) (open ts B)
  end.

Lemma open_nil : forall T, open [] T = T.
Proof.
  induction T; simpl; try reflexivity.
  - destruct n; reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
Qed.

Inductive inst : scheme -> ty -> Prop :=
| Inst :
    forall n T ts,
      length ts = n ->
      inst (Sch n T) (open ts T).

Lemma inst_mono : forall T, inst (Mono T) T.
Proof.
  intros T. unfold Mono.
  pose proof (Inst 0 T [] eq_refl) as H.
  rewrite open_nil in H. exact H.
Qed.

Lemma inst_mono_inv : forall T T', inst (Mono T) T' -> T' = T.
Proof.
  intros T T' H. unfold Mono in H. inversion H; subst.
  match goal with
  | Hl : length ?l = 0 |- _ =>
      apply length_zero_iff_nil in Hl; subst; apply open_nil
  end.
Qed.

(* ------------------------------------------------------------------ *)
(* Terms                                                               *)
(* ------------------------------------------------------------------ *)

Inductive tm : Type :=
| TmVar : nat -> tm
| TmInt : nat -> tm
| TmAdd : tm -> tm -> tm
| TmLam : nat -> tm -> tm          (* no type annotation: Curry style *)
| TmApp : tm -> tm -> tm
| TmLet : nat -> tm -> tm -> tm.

Definition env := nat -> option scheme.
Definition empty : env := fun _ => None.
Definition extend (G : env) (x : nat) (Sg : scheme) : env :=
  fun y => if Nat.eqb x y then Some Sg else G y.

Lemma extend_eq : forall G x Sg, extend G x Sg x = Some Sg.
Proof. intros. unfold extend. now rewrite Nat.eqb_refl. Qed.

Lemma extend_neq : forall G x y Sg, x <> y -> extend G x Sg y = G y.
Proof.
  intros G x y Sg H. unfold extend.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma extend_shadow :
  forall G x S1 S2, forall y, extend (extend G x S1) x S2 y = extend G x S2 y.
Proof.
  intros G x S1 S2 y. unfold extend. destruct (Nat.eqb x y); reflexivity.
Qed.

Lemma extend_permute :
  forall G x y Sx Sy,
    x <> y ->
    forall z, extend (extend G x Sx) y Sy z = extend (extend G y Sy) x Sx z.
Proof.
  intros G x y Sx Sy Hneq z. unfold extend.
  destruct (Nat.eqb y z) eqn:Eyz; destruct (Nat.eqb x z) eqn:Exz; auto.
  apply Nat.eqb_eq in Eyz. apply Nat.eqb_eq in Exz. subst. contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(* Typing                                                              *)
(* ------------------------------------------------------------------ *)

Inductive has_type : env -> tm -> ty -> Prop :=
| TyVar :
    forall G x Sg T,
      G x = Some Sg ->
      inst Sg T ->
      has_type G (TmVar x) T
| TyInt :
    forall G n,
      has_type G (TmInt n) TInt
| TyAdd :
    forall G a b,
      has_type G a TInt ->
      has_type G b TInt ->
      has_type G (TmAdd a b) TInt
| TyLam :
    forall G x body T1 T2,
      has_type (extend G x (Mono T1)) body T2 ->
      has_type G (TmLam x body) (TArrow T1 T2)
| TyApp :
    forall G f a T1 T2,
      has_type G f (TArrow T1 T2) ->
      has_type G a T1 ->
      has_type G (TmApp f a) T2
(* Polymorphic let: e1 must be typeable at every instance of the scheme,
   and the body may use x at any of them. *)
| TyLet :
    forall G x e1 e2 n T0 T2,
      (forall ts, length ts = n -> has_type G e1 (open ts T0)) ->
      has_type (extend G x (Sch n T0)) e2 T2 ->
      has_type G (TmLet x e1 e2) T2.

Inductive value : tm -> Prop :=
| VInt : forall n, value (TmInt n)
| VLam : forall x body, value (TmLam x body).

Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | TmVar y => if Nat.eqb x y then s else TmVar y
  | TmInt n => TmInt n
  | TmAdd a b => TmAdd (subst x s a) (subst x s b)
  | TmLam y body => if Nat.eqb x y then TmLam y body else TmLam y (subst x s body)
  | TmApp f a => TmApp (subst x s f) (subst x s a)
  | TmLet y e1 e2 =>
      TmLet y (subst x s e1) (if Nat.eqb x y then e2 else subst x s e2)
  end.

Inductive step : tm -> tm -> Prop :=
| ST_AddInts : forall n m, step (TmAdd (TmInt n) (TmInt m)) (TmInt (n + m))
| ST_Add1 : forall a a' b, step a a' -> step (TmAdd a b) (TmAdd a' b)
| ST_Add2 : forall v a a', value v -> step a a' -> step (TmAdd v a) (TmAdd v a')
| ST_AppLam : forall x body v, value v -> step (TmApp (TmLam x body) v) (subst x v body)
| ST_App1 : forall f f' a, step f f' -> step (TmApp f a) (TmApp f' a)
| ST_App2 : forall v a a', value v -> step a a' -> step (TmApp v a) (TmApp v a')
| ST_LetValue : forall x v body, value v -> step (TmLet x v body) (subst x v body)
| ST_Let1 : forall x e1 e1' e2, step e1 e1' -> step (TmLet x e1 e2) (TmLet x e1' e2).

(* ------------------------------------------------------------------ *)
(* Structural lemmas about the environment                             *)
(* ------------------------------------------------------------------ *)

Lemma context_invariance :
  forall G G' t T,
    (forall x, G x = G' x) ->
    has_type G t T ->
    has_type G' t T.
Proof.
  intros G G' t T Heq H. generalize dependent G'.
  induction H; intros G' Heq.
  - eapply TyVar; [ rewrite <- Heq; eassumption | assumption ].
  - constructor.
  - constructor; auto.
  - apply TyLam. apply IHhas_type. intros y.
    unfold extend. destruct (Nat.eqb x y); auto.
  - eapply TyApp; eauto.
  - eapply TyLet.
    + intros ts Hlen. apply H0; [ exact Hlen | exact Heq ].
    + apply IHhas_type. intros y.
      unfold extend. destruct (Nat.eqb x y); auto.
Qed.

Definition env_extends (G G' : env) : Prop :=
  forall x Sg, G x = Some Sg -> G' x = Some Sg.

Lemma weakening :
  forall G G' t T,
    env_extends G G' ->
    has_type G t T ->
    has_type G' t T.
Proof.
  intros G G' t T Hext Hty. generalize dependent G'.
  induction Hty; intros G' Hext.
  - eapply TyVar; [ apply Hext; eassumption | assumption ].
  - constructor.
  - constructor; auto.
  - apply TyLam. apply IHHty. unfold env_extends in *.
    intros y Ty Hy. unfold extend in *.
    destruct (Nat.eqb x y); eauto.
  - eapply TyApp; eauto.
  - eapply TyLet.
    + intros ts Hlen. apply H0; [ exact Hlen | exact Hext ].
    + apply IHHty. unfold env_extends in *.
      intros y Ty Hy. unfold extend in *.
      destruct (Nat.eqb x y); eauto.
Qed.

Lemma weaken_empty :
  forall G t T, has_type empty t T -> has_type G t T.
Proof.
  intros G t T H. eapply weakening; eauto.
  unfold env_extends, empty. intros x Ty Hnone. discriminate Hnone.
Qed.

(* ------------------------------------------------------------------ *)
(* Substitution                                                        *)
(* ------------------------------------------------------------------ *)

(* The substituted value must be typeable at every instance of the scheme the
   variable was bound with.  For a monomorphic binding that is one type; for a
   let binding it is the whole family. *)
Lemma substitution_preserves_typing :
  forall t G x Sg v T,
    has_type (extend G x Sg) t T ->
    (forall T', inst Sg T' -> has_type empty v T') ->
    has_type G (subst x v t) T.
Proof.
  induction t; intros G x Sg v T Ht Hv; simpl; inversion Ht; subst.
  - (* TmVar *)
    destruct (Nat.eqb x n) eqn:Exn.
    + apply Nat.eqb_eq in Exn. subst.
      match goal with
      | Hl : extend _ _ _ _ = Some _ |- _ =>
          rewrite extend_eq in Hl; inversion Hl; subst
      end.
      apply weaken_empty. apply Hv.
      match goal with | Hi : inst _ _ |- _ => exact Hi end.
    + apply Nat.eqb_neq in Exn.
      eapply TyVar.
      * match goal with
        | Hl : extend _ _ _ _ = Some _ |- _ =>
            rewrite extend_neq in Hl by auto; exact Hl
        end.
      * match goal with | Hi : inst _ _ |- _ => exact Hi end.
  - (* TmInt *)
    constructor.
  - (* TmAdd *)
    constructor; [ eapply IHt1 | eapply IHt2 ]; eauto.
  - (* TmLam *)
    destruct (Nat.eqb x n) eqn:Exn.
    + apply Nat.eqb_eq in Exn. subst.
      apply TyLam.
      apply context_invariance with (G := extend (extend G n Sg) n (Mono T1)).
      * apply extend_shadow.
      * assumption.
    + apply Nat.eqb_neq in Exn.
      apply TyLam. eapply IHt with (Sg := Sg); [ | exact Hv ].
      apply context_invariance with (G := extend (extend G x Sg) n (Mono T1)).
      * apply extend_permute. exact Exn.
      * assumption.
  - (* TmApp *)
    eapply TyApp; [ eapply IHt1 | eapply IHt2 ]; eauto.
  - (* TmLet *)
    eapply TyLet.
    + intros ts Hlen. eapply IHt1 with (Sg := Sg); [ | exact Hv ].
      match goal with
      | Hp : forall l : list ty, _ |- _ => apply Hp; exact Hlen
      end.
    + destruct (Nat.eqb x n) eqn:Exn.
      * apply Nat.eqb_eq in Exn. subst.
        apply context_invariance with (G := extend (extend G n Sg) n (Sch n0 T0)).
        -- apply extend_shadow.
        -- assumption.
      * apply Nat.eqb_neq in Exn.
        eapply IHt2 with (Sg := Sg); [ | exact Hv ].
        apply context_invariance with (G := extend (extend G x Sg) n (Sch n0 T0)).
        -- apply extend_permute. exact Exn.
        -- assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Canonical forms                                                     *)
(* ------------------------------------------------------------------ *)

Lemma canonical_int :
  forall v, value v -> has_type empty v TInt -> exists n, v = TmInt n.
Proof.
  intros v Hv Ht. inversion Hv; subst; eauto. inversion Ht.
Qed.

Lemma canonical_arrow :
  forall v T1 T2,
    value v -> has_type empty v (TArrow T1 T2) -> exists x body, v = TmLam x body.
Proof.
  intros v T1 T2 Hv Ht. inversion Hv; subst.
  - inversion Ht.
  - eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Progress and preservation                                           *)
(* ------------------------------------------------------------------ *)

Theorem progress :
  forall t T, has_type empty t T -> value t \/ exists t', step t t'.
Proof.
  intros t T Ht. remember empty as G. induction Ht; subst.
  - (* TmVar: impossible in the empty environment *)
    unfold empty in H. discriminate.
  - left. constructor.
  - right.
    destruct IHHt1 as [Hv1 | [a' Ha']]; auto.
    + destruct IHHt2 as [Hv2 | [b' Hb']]; auto.
      * destruct (canonical_int a Hv1 Ht1) as [n ->].
        destruct (canonical_int b Hv2 Ht2) as [m ->].
        exists (TmInt (n + m)). constructor.
      * exists (TmAdd a b'). constructor; auto.
    + exists (TmAdd a' b). constructor; auto.
  - left. constructor.
  - destruct IHHt1 as [Hvf | [f' Hf']]; auto.
    + destruct IHHt2 as [Hva | [a' Ha']]; auto.
      * right. destruct (canonical_arrow f T1 T2 Hvf Ht1) as [x [body ->]].
        exists (subst x a body). constructor; auto.
      * right. exists (TmApp f a'). constructor; auto.
    + right. exists (TmApp f' a). constructor; auto.
  - (* TmLet: use the instance at a list of the right length *)
    assert (Hlen : length (repeat TInt n) = n) by apply repeat_length.
    destruct (H0 (repeat TInt n) Hlen eq_refl) as [Hv1 | [e1' He1']].
    + right. exists (subst x e1 e2). constructor; auto.
    + right. exists (TmLet x e1' e2). constructor; auto.
Qed.

Theorem preservation :
  forall t t' T, has_type empty t T -> step t t' -> has_type empty t' T.
Proof.
  intros t t' T Ht Hs. generalize dependent T.
  induction Hs; intros T0 Ht; inversion Ht; subst.
  - constructor.
  - constructor; [ apply IHHs; assumption | assumption ].
  - constructor; [ assumption | apply IHHs; assumption ].
  - (* beta *)
    match goal with
    | Hfun : has_type empty (TmLam x body) (TArrow _ _) |- _ => inversion Hfun; subst
    end.
    eapply substitution_preserves_typing; [ eassumption | ].
    intros T' Hi. apply inst_mono_inv in Hi. subst. assumption.
  - eapply TyApp; [ apply IHHs; eassumption | eassumption ].
  - eapply TyApp; [ eassumption | apply IHHs; eassumption ].
  - (* let of a value *)
    eapply substitution_preserves_typing; [ eassumption | ].
    intros T' Hi. inversion Hi; subst.
    match goal with
    | Hp : forall l : list ty, _ |- _ => apply Hp; reflexivity
    end.
  - (* let, evaluating the bound expression *)
    econstructor.
    + intros ts Hlen. apply IHHs.
      match goal with
      | Hp : forall l : list ty, _ |- _ => apply Hp; exact Hlen
      end.
    + eassumption.
Qed.

Theorem type_safety :
  forall t t' T, has_type empty t T -> step t t' -> has_type empty t' T.
Proof. apply preservation. Qed.

(* ------------------------------------------------------------------ *)
(* The polymorphism is real                                            *)
(* ------------------------------------------------------------------ *)

Definition id_tm : tm := TmLam 0 (TmVar 0).

(* id has the scheme  forall a. a -> a  *)
Definition id_scheme : scheme := Sch 1 (TArrow (TBound 0) (TBound 0)).

Lemma id_at_every_instance :
  forall ts, length ts = 1 -> has_type empty id_tm (open ts (TArrow (TBound 0) (TBound 0))).
Proof.
  intros ts Hlen. destruct ts as [| t ts']; simpl in Hlen; try discriminate.
  destruct ts' as [| u ts'']; simpl in Hlen; try discriminate.
  simpl. unfold id_tm. apply TyLam.
  eapply TyVar; [ apply extend_eq | apply inst_mono ].
Qed.

(*  let id = fun x -> x in (id id) 42
    The first occurrence of id is used at (int -> int) -> (int -> int),
    the second at int -> int.  A monomorphic let cannot type this. *)
Definition poly_program : tm :=
  TmLet 1 id_tm (TmApp (TmApp (TmVar 1) (TmVar 1)) (TmInt 42)).

Lemma poly_program_typed :
  has_type empty poly_program TInt.
Proof.
  unfold poly_program.
  eapply TyLet with (n := 1) (T0 := TArrow (TBound 0) (TBound 0)).
  - apply id_at_every_instance.
  - eapply TyApp with (T1 := TInt).
    + eapply TyApp with (T1 := TArrow TInt TInt).
      * eapply TyVar; [ apply extend_eq | ].
        pose proof (Inst 1 (TArrow (TBound 0) (TBound 0))
                         [TArrow TInt TInt] eq_refl) as H.
        simpl in H. exact H.
      * eapply TyVar; [ apply extend_eq | ].
        pose proof (Inst 1 (TArrow (TBound 0) (TBound 0)) [TInt] eq_refl) as H.
        simpl in H. exact H.
    + constructor.
Qed.

(* The same program is not typeable if the binding is kept monomorphic:
   the two occurrences would have to receive the same type. *)
Lemma poly_program_needs_polymorphism :
  forall T,
    inst (Mono T) (TArrow (TArrow TInt TInt) (TArrow TInt TInt)) ->
    inst (Mono T) (TArrow TInt TInt) ->
    False.
Proof.
  intros T H1 H2.
  apply inst_mono_inv in H1. apply inst_mono_inv in H2. subst. discriminate.
Qed.

Lemma poly_program_steps :
  exists t', step poly_program t' /\ has_type empty t' TInt.
Proof.
  exists (subst 1 id_tm (TmApp (TmApp (TmVar 1) (TmVar 1)) (TmInt 42))).
  split.
  - unfold poly_program. apply ST_LetValue. unfold id_tm. constructor.
  - eapply preservation.
    + apply poly_program_typed.
    + unfold poly_program. apply ST_LetValue. unfold id_tm. constructor.
Qed.
