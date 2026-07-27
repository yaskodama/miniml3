From Coq Require Import Bool.Bool Arith.PeanoNat Lists.List.
Import ListNotations.

Inductive ty : Type :=
| TInt : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| TVar : nat -> tm
| TIntLit : nat -> tm
| TAdd : tm -> tm -> tm
| TLam : nat -> ty -> tm -> tm
| TApp : tm -> tm -> tm
| TLet : nat -> tm -> tm -> tm.

Definition env := nat -> option ty.
Definition empty : env := fun _ => None.
Definition extend (G : env) (x : nat) (T : ty) : env :=
  fun y => if Nat.eqb x y then Some T else G y.

Lemma extend_eq :
  forall G x T, extend G x T x = Some T.
Proof.
  intros. unfold extend. now rewrite Nat.eqb_refl.
Qed.

Lemma extend_neq :
  forall G x y T, x <> y -> extend G x T y = G y.
Proof.
  intros. unfold extend.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Inductive has_type : env -> tm -> ty -> Prop :=
| TyVar :
    forall G x T,
      G x = Some T ->
      has_type G (TVar x) T
| TyInt :
    forall G n,
      has_type G (TIntLit n) TInt
| TyAdd :
    forall G a b,
      has_type G a TInt ->
      has_type G b TInt ->
      has_type G (TAdd a b) TInt
| TyLam :
    forall G x TArg body TBody,
      has_type (extend G x TArg) body TBody ->
      has_type G (TLam x TArg body) (TArrow TArg TBody)
| TyApp :
    forall G f a TArg TBody,
      has_type G f (TArrow TArg TBody) ->
      has_type G a TArg ->
      has_type G (TApp f a) TBody
| TyLet :
    forall G x e1 e2 T1 T2,
      has_type G e1 T1 ->
      has_type (extend G x T1) e2 T2 ->
      has_type G (TLet x e1 e2) T2.

Inductive value : tm -> Prop :=
| VInt : forall n, value (TIntLit n)
| VLam : forall x T body, value (TLam x T body).

Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | TVar y => if Nat.eqb x y then s else TVar y
  | TIntLit n => TIntLit n
  | TAdd a b => TAdd (subst x s a) (subst x s b)
  | TLam y T body =>
      if Nat.eqb x y then TLam y T body else TLam y T (subst x s body)
  | TApp f a => TApp (subst x s f) (subst x s a)
  | TLet y e1 e2 =>
      TLet y (subst x s e1)
        (if Nat.eqb x y then e2 else subst x s e2)
  end.

Inductive step : tm -> tm -> Prop :=
| ST_AddInts :
    forall n m,
      step (TAdd (TIntLit n) (TIntLit m)) (TIntLit (n + m))
| ST_Add1 :
    forall a a' b,
      step a a' ->
      step (TAdd a b) (TAdd a' b)
| ST_Add2 :
    forall v a a',
      value v ->
      step a a' ->
      step (TAdd v a) (TAdd v a')
| ST_AppLam :
    forall x T body v,
      value v ->
      step (TApp (TLam x T body) v) (subst x v body)
| ST_App1 :
    forall f f' a,
      step f f' ->
      step (TApp f a) (TApp f' a)
| ST_App2 :
    forall v a a',
      value v ->
      step a a' ->
      step (TApp v a) (TApp v a')
| ST_LetValue :
    forall x v body,
      value v ->
      step (TLet x v body) (subst x v body)
| ST_Let1 :
    forall x e1 e1' e2,
      step e1 e1' ->
      step (TLet x e1 e2) (TLet x e1' e2).

Lemma context_invariance :
  forall G G' t T,
    (forall x, G x = G' x) ->
    has_type G t T ->
    has_type G' t T.
Proof.
  intros G G' t T Heq H.
  generalize dependent G'.
  induction H; intros G' Heq.
  - apply TyVar. now rewrite <- Heq.
  - constructor.
  - constructor; auto.
  - apply TyLam.
    apply IHhas_type. intros y.
    unfold extend. destruct (Nat.eqb x y); auto.
  - eapply TyApp; eauto.
  - eapply TyLet.
    + apply IHhas_type1. exact Heq.
    + apply IHhas_type2. intros y.
      unfold extend. destruct (Nat.eqb x y); auto.
Qed.

Definition env_extends (G G' : env) : Prop :=
  forall x T, G x = Some T -> G' x = Some T.

Lemma weakening :
  forall G G' t T,
    env_extends G G' ->
    has_type G t T ->
    has_type G' t T.
Proof.
  intros G G' t T Hext Hty.
  generalize dependent G'.
  induction Hty; intros G' Hext.
  - apply TyVar. eauto.
  - constructor.
  - constructor; auto.
  - apply TyLam.
    apply IHHty. unfold env_extends in *.
    intros y Ty Hy.
    unfold extend in *.
    destruct (Nat.eqb x y); eauto.
  - eapply TyApp; eauto.
  - eapply TyLet.
    + apply IHHty1. exact Hext.
    + apply IHHty2. unfold env_extends in *.
      intros y Ty Hy.
      unfold extend in *.
      destruct (Nat.eqb x y); eauto.
Qed.

Lemma weaken_empty :
  forall G t T,
    has_type empty t T ->
    has_type G t T.
Proof.
  intros G t T H.
  eapply weakening; eauto.
  unfold env_extends, empty.
  intros x Ty Hnone. discriminate Hnone.
Qed.

Lemma extend_shadow :
  forall G x T1 T2,
    (forall y, extend (extend G x T1) x T2 y = extend G x T2 y).
Proof.
  intros G x T1 T2 y. unfold extend.
  destruct (Nat.eqb x y); reflexivity.
Qed.

Lemma extend_permute :
  forall G x y Tx Ty,
    x <> y ->
    (forall z, extend (extend G x Tx) y Ty z = extend (extend G y Ty) x Tx z).
Proof.
  intros G x y Tx Ty Hneq z.
  unfold extend.
  destruct (Nat.eqb y z) eqn:Eyz; destruct (Nat.eqb x z) eqn:Exz; auto.
  apply Nat.eqb_eq in Eyz.
  apply Nat.eqb_eq in Exz.
  subst. contradiction.
Qed.

Lemma substitution_preserves_typing :
  forall G x U t v T,
    has_type (extend G x U) t T ->
    has_type empty v U ->
    has_type G (subst x v t) T.
Proof.
  intros G x U t v T Ht Hv.
  generalize dependent G.
  generalize dependent T.
  induction t; intros T G Ht; simpl; inversion Ht; subst.
  - destruct (Nat.eqb x n) eqn:Exn.
    + apply Nat.eqb_eq in Exn. subst.
      rewrite extend_eq in H1. inversion H1; subst.
      apply weaken_empty. exact Hv.
    + apply TyVar.
      apply Nat.eqb_neq in Exn.
      rewrite extend_neq in H1 by auto. exact H1.
  - constructor.
  - constructor.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - destruct (Nat.eqb x n) eqn:Exn.
    + apply TyLam.
      apply context_invariance with (G := extend (extend G x U) n t).
      * apply Nat.eqb_eq in Exn. subst.
        apply extend_shadow.
      * match goal with
        | Hbody : has_type (extend (extend G x U) n t) _ _ |- _ => exact Hbody
        end.
    + apply TyLam.
      apply IHt.
      apply context_invariance with (G := extend (extend G x U) n t).
      * apply Nat.eqb_neq in Exn.
        apply extend_permute. exact Exn.
      * match goal with
        | Hbody : has_type (extend (extend G x U) n t) _ _ |- _ => exact Hbody
        end.
  - eapply TyApp.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - eapply TyLet.
    + eapply IHt1; eauto.
    + destruct (Nat.eqb x n) eqn:Exn.
      * apply context_invariance with (G := extend (extend G x U) n T1).
        -- apply Nat.eqb_eq in Exn. subst.
           apply extend_shadow.
        -- match goal with
           | Hbody : has_type (extend (extend G x U) n T1) _ _ |- _ => exact Hbody
           end.
      * apply IHt2.
        apply context_invariance with (G := extend (extend G x U) n T1).
        -- apply Nat.eqb_neq in Exn.
           apply extend_permute. exact Exn.
        -- match goal with
           | Hbody : has_type (extend (extend G x U) n T1) _ _ |- _ => exact Hbody
           end.
Qed.

Lemma canonical_int :
  forall v,
    value v ->
    has_type empty v TInt ->
    exists n, v = TIntLit n.
Proof.
  intros v Hv Ht. inversion Hv; subst; eauto.
  inversion Ht.
Qed.

Lemma canonical_arrow :
  forall v T1 T2,
    value v ->
    has_type empty v (TArrow T1 T2) ->
    exists x body, v = TLam x T1 body.
Proof.
  intros v T1 T2 Hv Ht. inversion Hv; subst.
  - inversion Ht.
  - inversion Ht; subst. eauto.
Qed.

Theorem progress :
  forall t T,
    has_type empty t T ->
    value t \/ exists t', step t t'.
Proof.
  intros t T Ht.
  remember empty as G.
  induction Ht; subst.
  - discriminate.
  - left. constructor.
  - right.
    destruct IHHt1 as [Hv1 | [a' Ha']]; auto.
    + destruct IHHt2 as [Hv2 | [b' Hb']]; auto.
      * destruct (canonical_int a Hv1 Ht1) as [n ->].
        destruct (canonical_int b Hv2 Ht2) as [m ->].
        exists (TIntLit (n + m)). constructor.
      * exists (TAdd a b'). constructor; auto.
    + exists (TAdd a' b). constructor; auto.
  - left. constructor.
  - destruct IHHt1 as [Hvf | [f' Hf']]; auto.
    + destruct IHHt2 as [Hva | [a' Ha']]; auto.
      * right.
        destruct (canonical_arrow f TArg TBody Hvf Ht1) as [x [body ->]].
        exists (subst x a body). constructor; auto.
      * right. exists (TApp f a'). constructor; auto.
    + right. exists (TApp f' a). constructor; auto.
  - destruct IHHt1 as [Hv1 | [e1' He1']]; auto.
    + right. exists (subst x e1 e2). constructor; auto.
    + right. exists (TLet x e1' e2). constructor; auto.
Qed.

Theorem preservation :
  forall t t' T,
    has_type empty t T ->
    step t t' ->
    has_type empty t' T.
Proof.
  intros t t' T Ht Hs.
  generalize dependent T.
  induction Hs; intros T0 Ht; inversion Ht; subst.
  - constructor.
  - constructor.
    + apply IHHs.
      match goal with
      | H : has_type empty a _ |- _ => exact H
      end.
    + match goal with
      | H : has_type empty b TInt |- _ => exact H
      end.
  - constructor.
    + match goal with
      | H : has_type empty v TInt |- _ => exact H
      end.
    + apply IHHs.
      match goal with
      | H : has_type empty a TInt |- _ => exact H
      end.
  - match goal with
    | Hfun : has_type empty (TLam x T body) (TArrow _ _) |- _ =>
        inversion Hfun; subst
    end.
    eapply substitution_preserves_typing; eauto.
  - eapply TyApp.
    + apply IHHs.
      match goal with
      | H : has_type empty f _ |- _ => exact H
      end.
    + match goal with
      | H : has_type empty a _ |- _ => exact H
      end.
  - eapply TyApp.
    + match goal with
      | H : has_type empty v _ |- _ => exact H
      end.
    + apply IHHs.
      match goal with
      | H : has_type empty a _ |- _ => exact H
      end.
  - eapply substitution_preserves_typing; eauto.
  - eapply TyLet.
    + apply IHHs.
      match goal with
      | H : has_type empty e1 _ |- _ => exact H
      end.
    + match goal with
      | H : has_type (extend empty x _) e2 _ |- _ => exact H
      end.
Qed.

Theorem type_safety :
  forall t t' T,
    has_type empty t T ->
    step t t' ->
    has_type empty t' T.
Proof.
  apply preservation.
Qed.

Definition plus_one : tm :=
  TLam 0 TInt (TAdd (TVar 0) (TIntLit 1)).

Definition sample_program : tm :=
  TLet 1 plus_one (TApp (TVar 1) (TIntLit 41)).

Lemma sample_program_typed :
  has_type empty sample_program TInt.
Proof.
  unfold sample_program, plus_one.
  eapply TyLet with (T1 := TArrow TInt TInt).
  - apply TyLam.
    constructor.
    + apply TyVar. apply extend_eq.
    + constructor.
  - eapply TyApp with (TArg := TInt).
    + apply TyVar. apply extend_eq.
    + constructor.
Qed.

Lemma sample_program_steps :
  exists t',
    step sample_program t' /\ has_type empty t' TInt.
Proof.
  exists (subst 1 plus_one (TApp (TVar 1) (TIntLit 41))).
  split.
  - unfold sample_program.
    apply ST_LetValue.
    unfold plus_one. constructor.
  - eapply preservation.
    + apply sample_program_typed.
    + unfold sample_program.
      apply ST_LetValue.
      unfold plus_one. constructor.
Qed.
