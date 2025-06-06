(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst.

Ltac multi_eassumption :=
  multimatch goal with
  | [h : ?t |- _ ] => exact h
  end.

Ltac mtea := try multi_eassumption.

Definition map_rev [A B : Type] (f : A -> B) (l : list A) :
  map f (List.rev l) = List.rev (map f l).
Proof.
Admitted.

Definition All_rev (A : Type) (P : A -> Type) (l : list A) :
  All P l -> All P (List.rev l).
Proof.
Admitted.

Definition Alli_rev (A : Type) (P : nat -> A -> Type) n (l : list A) :
  Alli (fun i => P (#|l| - i - 1)) n l -> Alli P n (List.rev l).
Proof.
Admitted.

Ltac cbn_length := repeat (rewrite
  ?length_app ?length_map ?List.length_rev ?repeat_length
  ?length_rev ?mapi_length ?mapi_rec_length ?Nat.add_0_r
);
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
  fun l => List.rev (map vassAR l).

Definition terms_of_cxt : context -> list term :=
  fun Γ => map decl_type (List.rev Γ).

Definition it_binder binder : list term -> term -> term :=
  fun l t => fold_right (fun t u => binder (mkBindAnn nAnon Relevant) t u) t l.

Definition it_tProd : list term -> term -> term :=
fun l t => fold_right (fun t u => tProd (mkBindAnn nAnon Relevant) t u) t l.

Definition it_tLambda : list term -> term -> term :=
fun l t => fold_right (fun t u => tLambda (mkBindAnn nAnon Relevant) t u) t l.

Definition tRels (start length : nat) : list term :=
  List.rev (map tRel (seq start length)).

Definition eq_prod {A B} (x : A * B) y z : x = (y,z) -> (fst x = y) * (snd x = z).
Proof. destruct x; cbn. now intros [=]. Qed.


(* Functions on All and variants *)

(* All *)
Definition All_sym_inv : forall {A B C : Type} (f : A -> C) (g : B -> C)
  l l',
  All2 (fun y x => f x = g y) l' l ->
  All2 (fun x y => f x = g y) l  l'.
Proof.
  intros * X; induction X; constructor; eauto.
Qed.

Definition All_impl2 {A P Q1 Q2} {l : list A} :
  All Q1 l -> All Q2 l ->
  (forall x, Q1 x -> Q2 x -> P x) ->
  All P l.
Proof.
  intros H; induction H; intros q; inversion q; constructor; eauto.
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
  All P (List.rev (map f ((seq start length)))).
Proof.
  revert start; induction length; cbn [seq map]; intros start H.
  + constructor.
  + cbn. apply All_app_inv.
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

Fixpoint filter2 {A} (lb : list bool) (l : list A) : list A :=
  match lb, l with
  | [], [] => []
  | true::lb, a::l => a :: filter2 lb l
  | false::lb, a::l => filter2 lb l
  | _, _ => []
  end.

Definition All_filter2 {A} (P : A -> Type) lb l :
  All P l -> All P (filter2 lb l).
Proof.
  intros X; induction X in lb |- *; destruct lb as [|[] lb]; cbn;
  try constructor => //; auto.
Qed.

(* Alli *)
Definition Alli_impl {A : Type} {P Q : nat -> A -> Type} {l : list A} {n m : nat}:
  Alli Q n l -> (forall i x, Q (n + i) x -> P (m + i) x) -> Alli P m l.
Proof.
Admitted.

Definition Alli_map {A B P} {f : A -> B} {n l} :
  Alli (fun i x => P i (f x)) n l ->
  Alli P n (map f l).
Proof.
  intros H; induction H; constructor; eauto.
Qed.

Definition Alli_prod {A P1 P2 n} {l : list A} :
  Alli P1 n l ->  Alli P2 n l -> Alli (fun i n => P1 i n * P2 i n) n l.
Proof.
  intros X; induction X; intros Y; inversion Y; constructor; eauto.
Qed.

Definition Alli_map2 {A B P Q1 Q2} {f : A -> B} {n m k l} :
  Alli Q1 n l -> Alli Q2 m l ->
  (forall i x, Q1 (i + n) x -> Q2 (i + m) x -> P (i + k) (f x)) ->
  Alli P m (map f l).
Proof.
Admitted.

Definition Foo {A B P Q} {f : nat -> A -> B} {n m k l} :
  Alli Q n l ->
  (forall i x, Q (i + n) x -> P (i + m) (f (i + k) x)) ->
   Alli P m (mapi_rec f l k).
Proof.
  intros X.
  induction X in m,k |-; intros H; constructor.
  + apply H with (i := 0) => //.
  + cbn. apply IHX. intros i x; rewrite !Nat.add_succ_r. eapply H with (i := S i).
Qed.

Definition Alli_mapi_rec {A B P Q} {f : nat -> A -> B} {n m k l} :
  Alli Q n l ->
  (forall i x, Q (i + n) x -> P (i + m) (f (i + k) x)) ->
  Alli P m (mapi_rec f l k).
Proof.
  intros X.
  induction X in m,k |-; intros H; constructor.
  + apply H with (i := 0) => //.
  + eapply IHX; tea. intros i x; rewrite !Nat.add_succ_r. eapply H with (i := S i).
Qed.

Definition Alli_mapi {A B P Q} {f : nat -> A -> B} {n m l} :
  Alli Q n l ->
  (forall i x, Q (n + i) x -> P (m + i) (f i x)) ->
  Alli P m (mapi f l).
Proof.
  unfold mapi. intros H X.
  eapply Alli_mapi_rec; tea.
  intros. rewrite Nat.add_0_r. rewrite Nat.add_comm. apply X. rewrite Nat.add_comm //.
Qed.

Definition Alli_mapi_rec2 {A B P Q1 Q2} {f : nat -> A -> B} {n1 n2 m k l} :
  Alli Q1 n1 l -> Alli Q2 n2 l ->
  (forall i x, Q1 (i + n1) x -> Q2 (i + n2) x -> P (i + m) (f (i + k) x)) ->
  Alli P m (mapi_rec f l k).
Proof.
  intros X.
  induction X in n2,m,k |-; intros p2 H; inversion p2; constructor.
  + apply H with (i := 0) => //.
  + eapply IHX; tea. intros i x; rewrite !Nat.add_succ_r. eapply H with (i := S i).
Qed.

Definition Alli_mapi2 {A B P Q1 Q2} {f : nat -> A -> B} {n1 n2 m l} :
  Alli Q1 n1 l -> Alli Q2 n2 l ->
  (forall i x, Q1 (n1 + i) x -> Q2 (n2 + i) x -> P (m + i) (f i x)) ->
  Alli P m (mapi f l).
Proof.
  unfold mapi. intros p1 p2 H.
  unshelve eapply (Alli_mapi_rec2 p1 p2).
  intros. rewrite Nat.add_0_r. rewrite Nat.add_comm. apply H.
  all : rewrite Nat.add_comm //.
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

Definition All_telescope_prod {A} P Q (l : list A) :
  All_telescope (fun Γ arg => P Γ arg) l ->
  All_telescope (fun Γ arg => Q Γ arg) l ->
  All_telescope (fun Γ arg => P Γ arg * Q Γ arg) l.
Proof.
  intros H H2. induction H; cbn.
  1: constructor.
  inversion H2. 1: { apply (f_equal ( @length A)) in H1. rewrite length_app in H1; cbn in H1. lia. }
   apply app_inj_tail in H1 as []; subst. constructor; eauto.
Qed.

(* All2 *)
Definition All2_impl2 {A B : Type} {P Q1 Q2} l l':
  All2 Q1 l l' -> All2 Q2 l l' ->
  (forall (x : A) (y : B), Q1 x y -> Q2 x y -> P x y ) ->
    All2 P l l'.
Proof.
Admitted.

Definition All2_left_triv:
  forall {A B : Type} {l : list A} {l' : list B} (P : A -> Type),
  All P l -> #|l| = #|l'| -> All2 (fun x _ => P x) l l'.
Proof.
Admitted.


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
  remember (map check y.1) as lb eqn:Heqlb.
  revert y Heqlb pos_y.
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


(* list X * list X * y => old_args, new_args, data *)
Definition spec_fold_All_check2 {X Y}
  (* fct *)
  (check : X -> bool)
  (f : ( list X * list X * Y) -> X -> (list X * list X * Y))
  (xs : list X) (acc : list X * list X * Y)
  (* properties *)
  (PAcc : list X * list X * Y -> Type) (PX : list bool -> X -> Type)
  (pos_xs : All_check PX check (map check acc.1.1) xs)
  (pos_acc : PAcc acc)
  (inv_old : forall acc x, (f acc x).1.1 = acc.1.1 ++ [x])
  (pos_f : forall acc hd, PAcc acc -> PX (map check acc.1.1) hd -> PAcc (f acc hd))
  :
  PAcc (fold_left f xs acc).
Proof.
  remember (map check acc.1.1) as n.
  revert acc Heqn pos_acc.
  induction pos_xs; cbn. 1: easy.
  intros acc Heqn pos_acc.
  apply IHpos_xs.
  - rewrite inv_old map_app Heqn //.
  - apply pos_f => //. rewrite -Heqn => //.
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

From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICOnFreeVarsConv PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv.
From MetaRocq.PCUIC Require Import BDStrengthening.

Definition on_free_vars_andb P Q t :
  on_free_vars P t && on_free_vars Q t = on_free_vars (fun x => P x && Q x) t.
Proof.
Admitted.

Definition on_free_vars_impl2 {q1 q2 p : nat -> bool} {t} :
  (forall i, q1 i -> q2 i -> p i) ->
  on_free_vars q1 t -> on_free_vars q2 t ->  on_free_vars p t.
Proof.
  intros H Hq1 Hq2. eapply on_free_vars_impl with (p := fun i => q1 i && q2 i).
  1: { intros i [? ?]%andb_prop. apply H => //. }
  rewrite -on_free_vars_andb. apply andb_true_intro. by constructor.
Qed.

Definition shiftnP_impl_fct (p q : nat -> bool) f g:
  (forall i : nat, p (f i) -> q (g i)) ->
  forall n i : nat, shiftnP n p (f i) -> shiftnP n q (g i).
Proof.
Admitted.

(* Lemma for subst to move *)
Definition on_free_vars_subst P t k i s :
  All (on_free_vars (shiftnP k P)) s ->
  on_free_vars (shiftnP (k + i + #|s|) P) t ->
  on_free_vars (shiftnP (k + i) P) (subst s i t).
Proof.
  intros X%All_forallb H. rewrite Nat.add_comm. rewrite <- shiftnP_add.
  rewrite -(substP_shiftnP_gen _ #|s|).
  apply on_free_vars_subst_gen => //.
  rewrite shiftnP_add. apply_eq H. do 2 f_equal. lia.
Qed.

Definition on_free_vars_subst_eq P k i s m n t :
  m = k + i + #|s| ->
  n = k + i ->
  All (on_free_vars (shiftnP k P)) s ->
  on_free_vars (shiftnP m P) t ->
  on_free_vars (shiftnP n P) (subst s i t).
Proof.
  intros -> ->; apply on_free_vars_subst => //.
Qed.

Definition All_up_shift P n m l :
  n = m ->
  All (on_free_vars (shiftnP n P)) l ->
  All (on_free_vars (shiftnP m P)) l.
Proof.
  intros -> X; exact X.
Qed.

Definition Alli_up_start {A} (P : nat -> A -> Type) n m l :
  n = m ->
  Alli P n l ->
  Alli P m l.
Proof.
  intros -> X; exact X.
Qed.

Definition on_free_vars_up_shift P n m x :
  n = m ->
  on_free_vars (shiftnP n P) x ->
  on_free_vars (shiftnP m P) x.
Proof.
  intros -> X; exact X.
Qed.


Definition unlift_lift p k t :
  on_free_vars (shiftnP k (fun i => ~~ (i <? p))) t ->
  t = lift p k (unlift p k t).
Proof.
  intros X. induction t.
  + unfold unlift, unlift_renaming. cbn in *. unfold shiftnP in X.
    destruct (Nat.ltb_spec (n - k) p), (Nat.ltb_spec n k).
    - replace (k <=? n) with false by lia. reflexivity.
    - inversion X.
    - replace (k <=? n ) with false by lia. reflexivity.
    - replace (k <=? n - p) with true by lia. f_equal. lia.
  + admit.
Admitted.

(* Strengthening *)
Definition strengthen_renaming k f : nat -> nat :=
  fun n => if n <? k then n else f (n - k).

(* Definition strengthen_term k : term -> term :=
  rename (strengthen_renaming k (fun n => n)) 0.

Definition strengthen_pred k P : nat -> bool :=
  fun n => P (n + k). *)

(* Definition on_free_vars_strengthen P k t :
  on_free_vars (fun n => k-1 <? n) t ->
  on_free_vars P t ->
  on_free_vars (strengthen_pred k P) (strengthen_term k t).
Proof.
  intros Hnotin Ht.
  assert (Hboth : on_free_vars (fun n => P n && (k - 1 <? n)) t).
    1: { rewrite -on_free_vars_andb. apply andb_true_intro. constructor => //. }
  rewrite on_free_vars_rename. eapply on_free_vars_impl; only 2 : exact Hboth; cbn.
  unfold strengthen_pred, strengthen_renaming.
  intros i. intros [Pi ki]%andb_prop.
  assert (i <? k = false) as -> by lia.
  replace (i - k + k) with i by lia; done.
Qed. *)

(* Definition on_free_vars_shiftn_strengthen P k t :
  on_free_vars (fun n => k-1 <? n) t ->
  on_free_vars (shiftnP k P) t ->
  on_free_vars P (strengthen_term k t).
Proof.
  intros Hnotin Ht.
  rewrite on_free_vars_rename.
  refine (on_free_vars_impl2 _ Hnotin Ht).
  unfold shiftnP, strengthen_renaming.
  intros i ki [ik | Pik]%orb_prop; hnf in ki; try lia.
  assert (i <? k = false) as -> by lia.
  replace (i - k + k) with i by lia; done.
Qed. *)

(* Definition strengthen_k_pos Γ Δ lax nb_binders arg k :
  on_free_vars_argument (fun n => k -1 <? n) arg ->
  positive_argument nb_block up nup (Γ ++ Δ) lax nb_binders arg ->
  positive_argument nb_block up nup Γ lax nb_binders (strengthen_argument #|Δ| arg).
Proof.
Admitted. *)



(*
rename (shiftn k f) t =>>
  k + f (n - k) | k -- 0

rename (shiftn k f) (lift i k) (tRel n) =>>
    n <= k  =>   k
    n > k   =>   k + f (n + i - k)

rename (shiftn k (strengthen_renaming i g)) (lift i k) (tRel n) =>>
    n <= k  =>   k
    n > k   =>   k + f (n + i - k -i) = k + f (n - k)
  = rename (shiftn k g)

For k = 0, shiftn k = id =>>
  rename (strengthen_renaming n f) (lift0 n t) = (rename f t)
  => f (i + n -n) = f (i)
*)
    Definition shiftn_strengthen n k f t :
        rename (shiftn k (strengthen_renaming n f)) (lift n k t)
      = (rename (shiftn k f) t).
    Proof.
      induction t ; cbn.
      + unfold shiftn, strengthen_renaming; cbn.
        destruct (Nat.ltb_spec k n0); f_equal.
        - assert (k <=? n0 = true) as -> by lia.
          assert (n + n0 <? k = false) as -> by lia.
          assert (n0 <? k = false) as -> by lia.
          assert (n + n0 - k <? n = false) as -> by lia.
          replace (n + n0 - k - n) with (n0 - k) by lia.
          reflexivity.
        - destruct (Nat.leb_spec k n0).
          * assert (n + n0 <? k = false) as -> by lia.
            assert (n + n0 - k <? n = false) as -> by lia.
            assert (n0 <? k = false) as -> by lia.
            replace (n + n0 - k - n) with (n0 - k) by lia.
            reflexivity.
          * assert (n0 <? k = true) as -> by lia.
            reflexivity.
    Admitted.

(*
(* Tests *)
Definition try1 := [false; false; true; false; true; true; false].

Definition cpt_args2 (acc : list bool * (nat -> nat)) (b : bool)
    : list bool * (nat -> nat) :=
  if b
  then (acc.1, strengthen_renaming 1 acc.2)
  else (acc.1 ++ [b], shiftn 1 acc.2).

Definition ff2 : nat -> nat
  := (fold_left cpt_args2 try1 ([],fun n => n)).2.

(*
-------------------------------------
| 8 | 7 | 6 | 5 | 4 | 3 | 2 | 1 | 0 |
-------------------------------------
| 5 | 4 | 3 | 2 | X | 1 | X | X | 0 |
-------------------------------------
*)

Compute (ff2 8). Compute (ff2 7). Compute (ff2 6). Compute (ff2 5).
Compute (ff2 4). Compute (ff2 3). Compute (ff2 2). Compute (ff2 1). Compute (ff2 0).
*)


  (* lemma for binders *)
  (* already existing ??? on_free_vars directly *)
  Definition on_free_vars_tProd P k l t :
    Alli (fun i => on_free_vars (shiftnP i P)) k l ->
    on_free_vars (shiftnP (k + #|l|) P) t ->
    on_free_vars (shiftnP k P) (it_tProd l t).
  Proof.
    todo " totod".
  Qed.

  Definition on_free_vars_tLambda P k l t :
    Alli (fun i => on_free_vars (shiftnP i P)) k l ->
    on_free_vars (shiftnP (k + #|l|) P) t ->
    on_free_vars (shiftnP k P) (it_tLambda l t).
  Proof.
    todo " totod".
  Qed.

  Definition on_free_vars_tLambda_eq P k l t m :
    m = k + #|l| ->
    Alli (fun i => on_free_vars (shiftnP i P)) k l ->
    on_free_vars (shiftnP m P) t ->
    on_free_vars (shiftnP k P) (it_tLambda l t).
  Proof.
    todo " totod".
  Qed.

  Definition on_free_vars_mkApps P k u vs :
    All (on_free_vars (shiftnP k P)) vs ->
    on_free_vars (shiftnP k P) u ->
    on_free_vars (shiftnP k P) (mkApps u vs).
  Proof.
    todo " totod".
  Qed.



(* tactic *)
From Ltac2 Require Import Ltac2 Printf.

Ltac2 nconstructor n :=
  Control.extend (List.init n (fun i => fun _ => econstructor (Int.add 1 i)))
  (fun _ => ()) [].