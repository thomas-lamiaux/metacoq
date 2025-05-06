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


Inductive All_telescope {A : Type} (P : list A -> A -> Type)
  : list A -> Type :=
  | All_telescope_nil : All_telescope P []
  | All_telescope_cons : forall (d : A) (Γ : list A),
      All_telescope P Γ -> P Γ d -> All_telescope P (Γ ++ [d]).

Definition All_telescope_singleton {A : Type} (P : list A -> A -> Type) a :
  P [] a -> All_telescope P [a].
Proof.
  change [a] with ([] ++ [a]). repeat constructor => //.
Qed.

Definition All_telescope_app_inv {A P} {l l' : list A} :
  All_telescope P l -> All_telescope (fun Γ => P (l ++ Γ)) l' -> All_telescope P (l ++ l').
Proof.
  intros x y. revert x. induction y.
  - rewrite app_nil_r //.
  - rewrite app_assoc. constructor; eauto.
Qed.

Definition All_telescope_impl {A : Type} {P Q : list A -> A -> Type} {l : list A} :
  All_telescope P l -> (forall Γ x, P Γ x -> Q Γ x) -> All_telescope Q l.
Proof.
  intros x; induction x; constructor; eauto.
Qed.

Definition All_telescope_map {A B P Q} {f : A -> B} {l} :
  (forall x Γ, Q Γ x -> P (map f Γ) (f x)) ->
  All_telescope Q l -> All_telescope P (map f l).
Proof.
  intros Hf Hl.
  induction Hl. constructor.
  rewrite map_app; cbn.
  apply All_telescope_app_inv => //.
  apply All_telescope_singleton. rewrite app_nil_r.
  apply Hf => //.
Qed.

Definition All_telescope_to_Alli {A} P (l : list A) n :
  Alli P n l ->
  All_telescope (fun Γ => P (n + #|Γ|)) l.
Proof.
  clear.
  intros H. induction H; cbn. 1: constructor.
  change (hd :: tl) with ([hd] ++ tl).
  apply All_telescope_app_inv => //; cbn.
  - apply All_telescope_singleton; cbn. cbn_length => //.
  - eapply All_telescope_impl; tea; cbn. intros.
    rewrite Nat.add_succ_r //.
Qed.



Inductive All_check {A : Type} (P : list bool -> A -> Type) check lb : list A -> Type :=
| All_check_nil2 : All_check P check lb []
| All_check_cons2 : forall (d : A) (Γ : list A),
    P lb d -> All_check P check (lb ++ [check d]) Γ -> All_check P check lb (d :: Γ).

Definition spec_fold_All_check {X Y} (check : X -> bool) (f : ((list X) * Y) -> X -> ((list X) * Y)) (xs : list X) (y : (list X) * Y)
  (PY : list X * Y -> Type) (PX : list bool -> X -> Type)
  (pos_xs : All_check PX check (map check y.1) xs)
  (pos_y : PY y)
  (length_f : forall y x, map check (f y x).1 = map check y.1 ++ [check x])
  (pos_f : forall y hd, PY y -> PX (map check y.1) hd -> PY (f y hd))
  :
  PY (fold_left f xs y).
Proof.
  remember (map check y.1) as n.
  revert y Heqn pos_y.
  induction pos_xs; cbn. 1: easy.
  intros y Heqn pos_y.
  apply IHpos_xs.
  - rewrite length_f Heqn //.
  - apply pos_f => //. rewrite -Heqn => //.
Qed.


Definition All_check_app_inv {A P} check acc (l1 l2 : list A) :
  All_check P check acc l1 ->
  All_check P check (acc ++ map check l1) l2 ->
  All_check P check acc (l1 ++ l2).
Proof.
  intros X; revert l2; induction X; cbn.
  - rewrite app_nil_r. easy.
  - intros l2 H. constructor => //. apply IHX.
    rewrite -app_assoc //.
Qed.

Definition All_telescope_to_All_check {X} P check (l : list X):
  All_telescope (fun Γ => P (map check Γ)) l ->
  All_check P check [] l.
Proof.
  intros H. induction H. constructor.
  apply All_check_app_inv => //.
  cbn. repeat constructor. done.
Qed.



Definition spec_fold_Alli {X Y} (f : ((list X) * Y) -> X -> ((list X) * Y)) (xs : list X) (y : (list X) * Y)
  (PY : list X * Y -> Type) (PX : nat -> X -> Type)
  (pos_xs : Alli PX #|y.1| xs)
  (pos_y : PY y)
  (length_f : forall y x, #|(f y x).1| = S #|y.1|)
  (pos_f : forall y hd, PY y -> PX #|y.1| hd -> PY (f y hd))
  :
  PY (fold_left f xs y).
Proof.
  remember (#|y.1|) as n.
  revert y Heqn pos_y.
  induction pos_xs; cbn. 1: easy.
  intros y Heqn pos_y.
  apply IHpos_xs.
  - rewrite length_f. lia.
  - apply pos_f => //. rewrite -Heqn => //.
Qed.

From Ltac2 Require Import Ltac2 Printf.

Ltac2 nconstructor n :=
  Control.extend (List.init n (fun i => fun _ => econstructor (Int.add 1 i)))
  (fun _ => ()) [].