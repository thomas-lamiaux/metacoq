(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst.

Definition map_rev [A B : Type] (f : A -> B) (l : list A) :
  map f (rev l) = rev (map f l).
Proof.
Admitted.

Check map_rev.

Definition All_rev (A : Type) (P : A -> Type) (l : list A) :
  All P l -> All P (rev l).
Proof.
Admitted.

Ltac cbn_length := repeat (rewrite ?length_app ?length_map ?List.length_rev ?length_rev ?mapi_length ?mapi_rec_length ?Nat.add_0_r);
repeat (rewrite ?Nat.add_assoc).

Tactic Notation "solve_length" := solve [cbn_length; lia].
Tactic Notation "solve_length_using" tactic(t) := solve [cbn_length; t; lia].

Ltac apply_eq H :=
  let feq := fresh "feq" in
  eassert (feq : _ = _); only 2: (rewrite <- feq; apply H); only 1 : f_equal.

(* Tactic Notation "apply_eq" ident(H) := (apply_eq H).

Ltac apply_eq_by H tac :=
  let feq := fresh "feq" in
  eassert (feq : _ = _); only 2: (rewrite <- feq; apply H); only 1 : (f_equal; tac).

Tactic Notation "apply_eq" ident(H) "by" tactic(tac) := (apply_eq_by H tac). *)

Ltac eapply_eq H :=
  let feq := fresh "feq" in
  eassert (feq : _ = _); only 2: (rewrite <- feq; eapply H); only 1 : f_equal.

(* Ltac eapply_eq_by H tac :=
  let feq := fresh "feq" in
  eassert (feq : _ = _); only 2: (rewrite <- feq; eapply H); only 1 : (f_equal; tac).

Tactic Notation "eapply_eq" ident(H) "by" tactic(tac) := (eapply_eq_by H tac). *)




(* Functions on terms *)
Definition test_tVar := [tVar "foo1"; tVar "foo2"; tVar "foo3"].

Definition vassAR : term -> context_decl :=
  fun t => vass (mkBindAnn nAnon Relevant) t.

Definition cxt_of_terms : list term -> context :=
  fun l => rev (map vassAR l).

Definition terms_of_cxt : context -> list term :=
  fun Γ => map decl_type (rev Γ).

Definition it_binder binder : list term -> term -> term :=
  fun l t => fold_right (fun t u => binder (mkBindAnn nAnon Relevant) t u) t l.

Definition it_tProd : list term -> term -> term :=
fun l t => fold_right (fun t u => tProd (mkBindAnn nAnon Relevant) t u) t l.

Definition it_tLambda : list term -> term -> term :=
fun l t => fold_right (fun t u => tLambda (mkBindAnn nAnon Relevant) t u) t l.

Definition tRels (start length : nat) : list term :=
  rev (map tRel (seq start length)).

Definition eq_prod {A B} (x : A * B) y z : x = (y,z) -> (fst x = y) * (snd x = z).
Proof. destruct x; cbn. now intros [=]. Qed.


(* Functions on All and variants *)

(* All *)
Definition All_map {A B P Q} {f : A -> B} {l} :
  (forall x, Q x -> P (f x)) ->
  All Q l -> All P (map f l).
Proof.
  intros H p; induction p; constructor; eauto.
Qed.

Definition All_pointwise_map {A P} {f : nat -> A} {start length} :
  (forall i, start <= i -> i < start + length -> P (f i)) ->
    All P (map f ((seq start length))).
  Proof.
    revert start; induction length; cbn; intros start H; constructor.
    - apply H; lia.
    - apply IHlength. intros. apply H; lia.
  Qed.

Definition All_rev_pointwise_map {A P} {f : nat -> A} {start length} :
(forall i, start <= i -> i < start + length -> P (f i)) ->
  All P (rev (map f ((seq start length)))).
Proof.
  revert start; induction length; cbn [seq map]; intros start H.
  + constructor.
  + rewrite rev_cons. apply All_app_inv.
    - apply IHlength. intros. apply H; lia.
    - repeat constructor. apply H; lia.
Qed.

Definition All_nth {A} P (l : list A) a k :
  k < #|l| ->
  All P l -> P (nth k l a).
Proof.
Admitted.


(* All2 *)
Definition All2_nth {A B} P (lA : list A) (lB : list B) k a b :
  k < #|lA| ->
  All2 P lA lB -> P (nth k lA a) (nth k lB b).
Proof.
Admitted.


(* Alli *)
Definition Alli_map {A B P Q} {f : A -> B} {n l} :
  (forall n x, Q n x -> P n (f x)) ->
  Alli Q n l -> Alli P n (map f l).
Proof.
  intros H p; induction p; constructor; eauto.
Qed.

Definition Alli_map_gen {A B P Q} {f : A -> B} {n k l} :
  (forall n x, Q n x -> P (n + k) (f x)) ->
  Alli Q n l -> Alli P (n + k) (map f l).
Proof.
  intros H p; induction p; constructor; eauto.
Qed.

Definition Alli_map_gen_eq {A B P Q} {f : A -> B} {n k l m} :
  m = n + k ->
  (forall n x, Q n x -> P (n + k) (f x)) ->
  Alli Q n l -> Alli P m (map f l).
Proof.
  intros -> H p; induction p; constructor; eauto.
Qed.

Definition Alli_mapi_rec {A B P Q} {f : nat -> A -> B} {k n m l} :
(forall i x, Q (k + i) x -> P (n + i) (f (i + m) x)) ->
Alli Q k l -> Alli P n (mapi_rec f l m).
Proof.
intros H x; revert m n H; induction x as [|k a l Qka]; cbn; constructor.
- apply_eq (H 0); only 1 : lia. apply_eq Qka; only 1: lia.
- apply IHx. intros. apply_eq (H (S i)); now rewrite Nat.add_succ_r.
Qed.

Definition Alli_mapi {A B P Q} {f : nat -> A -> B} {k n l} :
(forall i x, Q (k + i) x -> P (n + i) (f i x)) ->
Alli Q k l -> Alli P n (mapi f l).
Proof.
unfold mapi. intros H X.
eapply Alli_mapi_rec. 2: exact X.
intros. rewrite Nat.add_0_r. now apply H.
Qed.

Definition Alli_pointwise_mapi_rec {A P} {f : nat -> A} {n start length} :
  (forall i, start <= i -> i < start + length -> P (n + (i - start)) (f i)) ->
  Alli P n (map f ((seq start length))).
Proof.
  revert n start; induction length; cbn; intros n k H; constructor.
  - apply_eq H; lia.
  - apply IHlength. intros. apply_eq H; lia.
Qed.
