From Coq Require Import List Arith.PeanoNat Bool.Bool.
Import ListNotations.

(*
  Hindley-Milner inference soundness.

  What changed with respect to the first version of this file
  -----------------------------------------------------------
  The earlier development stubbed out the two rules that carry all of the
  content of Hindley-Milner:

      inst (Forall xs T) T           -- instantiation returned the body unchanged
      gen  G T (Forall xs T)         -- generalisation quantified anything at all

  With instantiation the identity and generalisation unconstrained, [hm_infer]
  and [has_type] were the same relation constructor for constructor, so
  [hm_infer_sound] held by mapping each constructor to its twin and said
  nothing.

  Here instantiation really substitutes for the quantified variables, and
  generalisation carries the Damas-Milner side condition: a variable may be
  quantified only if it is not free in the environment.  The declarative system
  keeps generalisation as a relation -- any scheme meeting the side condition --
  while the algorithm commits to the maximal one, [gen_max].  Soundness is then
  a real obligation: one has to show that what the algorithm computes satisfies
  the side condition the declarative system demands.  That is [gen_max_ok].

  Still out of scope, as before: a concrete unification algorithm, the occurs
  check, and principal types.  [InfLam] still guesses the argument type and
  [InfApp] still assumes the function already has an arrow type, which is the
  shape unification would deliver on success.
*)

(* ------------------------------------------------------------------ *)
(* Types, expressions, schemes                                         *)
(* ------------------------------------------------------------------ *)

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

(* [Sch xs T] is  forall xs. T *)
Inductive scheme : Type :=
| Sch : list nat -> ty -> scheme.

Definition Mono (T : ty) : scheme := Sch [] T.

(* Environments are association lists so that the free variables of an
   environment are computable, which the side condition on [gen] needs. *)
Definition env := list (nat * scheme).

Fixpoint lookup (G : env) (x : nat) : option scheme :=
  match G with
  | [] => None
  | (y, Sg) :: G' => if Nat.eqb y x then Some Sg else lookup G' x
  end.

(* ------------------------------------------------------------------ *)
(* Type substitution                                                   *)
(* ------------------------------------------------------------------ *)

Definition tsub := nat -> ty.
Definition tid : tsub := TVar.

Fixpoint appT (s : tsub) (T : ty) : ty :=
  match T with
  | TInt => TInt
  | TVar a => s a
  | TArrow A B => TArrow (appT s A) (appT s B)
  end.

Lemma appT_id :
  forall s, (forall a, s a = TVar a) -> forall T, appT s T = T.
Proof.
  intros s Hs T. induction T; simpl.
  - reflexivity.
  - apply Hs.
  - rewrite IHT1, IHT2. reflexivity.
Qed.

Lemma appT_tid : forall T, appT tid T = T.
Proof.
  intros T. apply appT_id. intros a. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Membership, free variables                                          *)
(* ------------------------------------------------------------------ *)

Definition memb (a : nat) (l : list nat) : bool := existsb (Nat.eqb a) l.

Lemma memb_In : forall a l, memb a l = true <-> In a l.
Proof.
  intros a l. unfold memb. rewrite existsb_exists. split.
  - intros [y [Hy Heq]]. apply Nat.eqb_eq in Heq. subst. exact Hy.
  - intros H. exists a. split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma memb_false_notin : forall a l, memb a l = false -> ~ In a l.
Proof.
  intros a l Hf Hin. apply memb_In in Hin. rewrite Hf in Hin. discriminate.
Qed.

Fixpoint ftv (T : ty) : list nat :=
  match T with
  | TInt => []
  | TVar a => [a]
  | TArrow A B => ftv A ++ ftv B
  end.

Definition ftv_scheme (Sg : scheme) : list nat :=
  match Sg with
  | Sch xs T => filter (fun a => negb (memb a xs)) (ftv T)
  end.

Fixpoint ftv_env (G : env) : list nat :=
  match G with
  | [] => []
  | (_, Sg) :: G' => ftv_scheme Sg ++ ftv_env G'
  end.

(* ------------------------------------------------------------------ *)
(* Instantiation: a real substitution for the quantified variables     *)
(* ------------------------------------------------------------------ *)

Definition only_on (xs : list nat) (s : tsub) : Prop :=
  forall a, memb a xs = false -> s a = TVar a.

Inductive inst : scheme -> ty -> Prop :=
| Inst :
    forall xs T s,
      only_on xs s ->
      inst (Sch xs T) (appT s T).

Lemma only_on_nil : forall s, only_on [] s -> forall a, s a = TVar a.
Proof.
  intros s H a. apply H. reflexivity.
Qed.

Lemma inst_mono : forall T, inst (Mono T) T.
Proof.
  intros T. unfold Mono.
  rewrite <- (appT_tid T) at 2.
  apply Inst. unfold only_on, tid. intros a _. reflexivity.
Qed.

(* A monomorphic scheme has exactly one instance, itself. *)
Lemma inst_mono_inv : forall T T', inst (Mono T) T' -> T' = T.
Proof.
  intros T T' H. unfold Mono in H. inversion H; subst.
  apply appT_id. apply only_on_nil. assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Generalisation, with the Damas-Milner side condition                *)
(* ------------------------------------------------------------------ *)

Inductive gen : env -> ty -> scheme -> Prop :=
| Gen :
    forall G T xs,
      (forall a, In a xs -> ~ In a (ftv_env G)) ->
      gen G T (Sch xs T).

(* What the algorithm commits to: quantify every variable of T that the
   environment does not hold fixed. *)
Definition gen_max (G : env) (T : ty) : scheme :=
  Sch (filter (fun a => negb (memb a (ftv_env G))) (ftv T)) T.

(* The obligation that makes soundness non-trivial. *)
Lemma gen_max_ok : forall G T, gen G T (gen_max G T).
Proof.
  intros G T. unfold gen_max. apply Gen.
  intros a Ha. apply filter_In in Ha. destruct Ha as [_ Hneg].
  apply negb_true_iff in Hneg.
  apply memb_false_notin. exact Hneg.
Qed.

(* ------------------------------------------------------------------ *)
(* Declarative typing                                                  *)
(* ------------------------------------------------------------------ *)

Inductive has_type : env -> expr -> ty -> Prop :=
| TyVar :
    forall G x Sg T,
      lookup G x = Some Sg ->
      inst Sg T ->
      has_type G (EVar x) T
| TyInt :
    forall G n,
      has_type G (EInt n) TInt
| TyLam :
    forall G x body T1 T2,
      has_type ((x, Mono T1) :: G) body T2 ->
      has_type G (ELam x body) (TArrow T1 T2)
| TyApp :
    forall G f a T1 T2,
      has_type G f (TArrow T1 T2) ->
      has_type G a T1 ->
      has_type G (EApp f a) T2
| TyLet :
    forall G x e1 e2 T1 Sg T2,
      has_type G e1 T1 ->
      gen G T1 Sg ->
      has_type ((x, Sg) :: G) e2 T2 ->
      has_type G (ELet x e1 e2) T2.

(* ------------------------------------------------------------------ *)
(* Algorithmic inference                                               *)
(* ------------------------------------------------------------------ *)

Inductive hm_infer : env -> expr -> ty -> Prop :=
| InfVar :
    forall G x Sg T,
      lookup G x = Some Sg ->
      inst Sg T ->
      hm_infer G (EVar x) T
| InfInt :
    forall G n,
      hm_infer G (EInt n) TInt
| InfLam :
    forall G x body T1 T2,
      hm_infer ((x, Mono T1) :: G) body T2 ->
      hm_infer G (ELam x body) (TArrow T1 T2)
| InfApp :
    forall G f a T1 T2,
      hm_infer G f (TArrow T1 T2) ->
      hm_infer G a T1 ->
      hm_infer G (EApp f a) T2
(* The algorithm does not get to choose a scheme: it computes gen_max. *)
| InfLet :
    forall G x e1 e2 T1 T2,
      hm_infer G e1 T1 ->
      hm_infer ((x, gen_max G T1) :: G) e2 T2 ->
      hm_infer G (ELet x e1 e2) T2.

Theorem hm_infer_sound :
  forall G e T,
    hm_infer G e T ->
    has_type G e T.
Proof.
  intros G e T H. induction H.
  - eapply TyVar; eauto.
  - constructor.
  - apply TyLam. exact IHhm_infer.
  - eapply TyApp; eauto.
  - eapply TyLet.
    + exact IHhm_infer1.
    + apply gen_max_ok.          (* here the side condition must be discharged *)
    + exact IHhm_infer2.
Qed.

(* ------------------------------------------------------------------ *)
(* The side condition is not vacuous                                   *)
(* ------------------------------------------------------------------ *)

(* A variable that the environment holds fixed may not be generalised. *)
Lemma gen_rejects_env_variable :
  ~ gen [(0, Sch [] (TVar 7))] (TVar 7) (Sch [7] (TVar 7)).
Proof.
  intros H. inversion H; subst.
  match goal with
  | Hc : forall a, In a _ -> ~ In a _ |- _ =>
      apply (Hc 7); simpl; left; reflexivity
  end.
Qed.

(* And the algorithm does not try to: on that environment it generalises
   nothing, so the scheme it builds is monomorphic. *)
Lemma gen_max_keeps_env_variable :
  gen_max [(0, Mono (TVar 7))] (TVar 7) = Mono (TVar 7).
Proof. reflexivity. Qed.

(* On the empty environment the same type is fully generalised. *)
Lemma gen_max_on_empty :
  gen_max [] (TVar 7) = Sch [7] (TVar 7).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Instantiation really substitutes                                    *)
(* ------------------------------------------------------------------ *)

Definition s_int : tsub := fun a => if Nat.eqb a 0 then TInt else TVar a.
Definition s_fun : tsub := fun a => if Nat.eqb a 0 then TArrow TInt TInt else TVar a.

Lemma only_on_s_int : only_on [0] s_int.
Proof.
  unfold only_on, s_int, memb. intros a Ha. simpl in Ha.
  destruct (Nat.eqb a 0) eqn:E; [discriminate | reflexivity].
Qed.

Lemma only_on_s_fun : only_on [0] s_fun.
Proof.
  unfold only_on, s_fun, memb. intros a Ha. simpl in Ha.
  destruct (Nat.eqb a 0) eqn:E; [discriminate | reflexivity].
Qed.

Definition id_scheme : scheme := Sch [0] (TArrow (TVar 0) (TVar 0)).

Lemma id_scheme_at_int :
  inst id_scheme (TArrow TInt TInt).
Proof.
  unfold id_scheme.
  replace (TArrow TInt TInt)
     with (appT s_int (TArrow (TVar 0) (TVar 0))) by reflexivity.
  apply Inst. apply only_on_s_int.
Qed.

Lemma id_scheme_at_fun :
  inst id_scheme (TArrow (TArrow TInt TInt) (TArrow TInt TInt)).
Proof.
  unfold id_scheme.
  replace (TArrow (TArrow TInt TInt) (TArrow TInt TInt))
     with (appT s_fun (TArrow (TVar 0) (TVar 0))) by reflexivity.
  apply Inst. apply only_on_s_fun.
Qed.

(* ------------------------------------------------------------------ *)
(* Genuine let-polymorphism: one binding used at two different types   *)
(* ------------------------------------------------------------------ *)

Definition id_e : expr := ELam 0 (EVar 0).

(*  let id = fun x -> x in (id id) 42  *)
Definition selfapp : expr :=
  ELet 1 id_e (EApp (EApp (EVar 1) (EVar 1)) (EInt 42)).

Lemma infer_id_e :
  hm_infer [] id_e (TArrow (TVar 0) (TVar 0)).
Proof.
  unfold id_e. apply InfLam.
  eapply InfVar.
  - simpl. reflexivity.
  - apply inst_mono.
Qed.

Lemma gen_max_id :
  gen_max [] (TArrow (TVar 0) (TVar 0)) = Sch [0; 0] (TArrow (TVar 0) (TVar 0)).
Proof. reflexivity. Qed.

Lemma only_on_s_int' : only_on [0; 0] s_int.
Proof.
  unfold only_on, s_int, memb. intros a Ha. simpl in Ha.
  destruct (Nat.eqb a 0) eqn:E; [discriminate | reflexivity].
Qed.

Lemma only_on_s_fun' : only_on [0; 0] s_fun.
Proof.
  unfold only_on, s_fun, memb. intros a Ha. simpl in Ha.
  destruct (Nat.eqb a 0) eqn:E; [discriminate | reflexivity].
Qed.

Lemma infer_selfapp :
  hm_infer [] selfapp TInt.
Proof.
  unfold selfapp.
  eapply InfLet.
  - apply infer_id_e.
  - rewrite gen_max_id.
    eapply InfApp with (T1 := TInt).
    + (* (id id) : int -> int, using id at two different types *)
      eapply InfApp with (T1 := TArrow TInt TInt).
      * eapply InfVar.
        -- simpl. reflexivity.
        -- replace (TArrow (TArrow TInt TInt) (TArrow TInt TInt))
              with (appT s_fun (TArrow (TVar 0) (TVar 0))) by reflexivity.
           apply Inst. apply only_on_s_fun'.
      * eapply InfVar.
        -- simpl. reflexivity.
        -- replace (TArrow TInt TInt)
              with (appT s_int (TArrow (TVar 0) (TVar 0))) by reflexivity.
           apply Inst. apply only_on_s_int'.
    + constructor.
Qed.

Theorem selfapp_sound :
  has_type [] selfapp TInt.
Proof.
  apply hm_infer_sound. exact infer_selfapp.
Qed.

(* The same program is not typeable if the let binding is kept monomorphic:
   the two occurrences of [id] would have to receive the same type. *)
Lemma selfapp_needs_polymorphism :
  forall T,
    inst (Mono T) (TArrow (TArrow TInt TInt) (TArrow TInt TInt)) ->
    inst (Mono T) (TArrow TInt TInt) ->
    False.
Proof.
  intros T H1 H2.
  apply inst_mono_inv in H1. apply inst_mono_inv in H2.
  subst. discriminate.
Qed.
