(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
(* From MetaRocq.Common Require Import BasicAst Primitive Universes Environment. *)
(* From Equations.Prop Require Import Classes EqDecInstances. *)
(* From Coq Require Import List. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICOnFreeVarsConv PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv.
Import PCUICEnvironment.
From MetaRocq.PCUIC Require Import PCUICAuxToMove PCUICViewInductive.
From MetaRocq.PCUIC Require Import BDStrengthening.
Import ViewInductive.

(* Todo list:

[X] 1. Specialize inductive block
    [X] 1.1 all but nested case
    [X] 1.2 nested case
    [X] 1.3 indices
      [X] change instantiation
      [X] filter indices
      [X] changes indices everywhere
[ ] 2. Proof positivity is preserved
    [X] 2.1 all but nested case
    [X] 2.2 nested case
    [X] 2.3 indices
    [ ] 2.4 modify pos cdt
[X] 3. Nested to Mutual
[X] 4. Positivity is preserved

Indices :
=> restrict args pos strict (i.e. no rec call)
=> suppose it, either add it to pos or prove it
=> proof should be the same except instantion to modify
  for strengthening + proof it is "pos"

*)

Definition on_free_vars_argument_subst_eq P k i s m n t :
  m = k + i + #|s| ->
  n = k + i ->
  All (on_free_vars (shiftnP k P)) s ->
  on_free_vars_argument (shiftnP m P) t ->
  on_free_vars_argument (shiftnP n P) (subst_argument s i t).
Proof.
Admitted.

Definition rc_notin_decrease {l l' nb_binders t} :
  All2 (fun a b => is_true (~~ a) -> is_true (~~ b)) l l' ->
  rc_notin_bool l  nb_binders t ->
  rc_notin_bool l' nb_binders t.
Proof.
  unfold rc_notin_bool, notin_of_rev_list.
  intros H. eapply on_free_vars_impl, shiftnP_impl.
  unfold is_true.
  induction H => //=. intros i.
  assert (Hll' : #|l| = #|l'|) by (eapply All2_length; tea).
  cbn in Hll'. unfold is_true.
  destruct (Nat.ltb_spec i #|l|).
  + rewrite !app_nth1; try solve_length. eauto.
  + destruct (Nat.ltb_spec i (S #|l|)).
    - assert (i = #|List.rev l|) as -> by solve_length.
      assert (#|List.rev l| = #|List.rev l'|) as Hll'Rev by solve_length.
      rewrite {2}Hll'Rev.
      rewrite !nth_middle. done.
    - rewrite !nth_overflow; try cbn_length; cbn; lia.
Qed.

Definition on_free_vars_xpredT {n t} : on_free_vars (shiftnP n xpredT) t.
Proof.
  rewrite shiftnP_xpredT.
Admitted.

Definition rc_notin_false {n nb_binders t} :
  rc_notin_bool (repeat false n) nb_binders t.
Proof.
  unfold rc_notin_bool, notin_of_rev_list.
  eapply on_free_vars_impl; only 2: apply (@on_free_vars_xpredT nb_binders).
  eapply shiftnP_impl. intros.
  rewrite -map_nth map_rev map_repeat rev_repeat nth_repeat.
  done.
Qed.

Definition shiftnP_impl2 (p q r : nat -> bool) :
  (forall i, p i -> q i -> r i) ->
  forall n i, shiftnP n p i -> shiftnP n q i -> shiftnP n r i.
Proof.
Admitted.

Definition rc_notin_app {l1 l2 n t} :
  rc_notin_bool l1 (#|l2| + n) t ->
  rc_notin_bool l2 n t ->
  rc_notin_bool (l1 ++ l2) n t.
Proof.
  unfold rc_notin_bool, notin_of_rev_list.
  eapply on_free_vars_impl2.
  intros i.
  rewrite Nat.add_comm -shiftnP_add.
  eapply shiftnP_impl2; clear i; unfold shiftnP.
  intros i rc_notin_l1 rc_notin_l2.
  rewrite rev_app_distr. unfold shiftnP in rc_notin_l1.
  destruct (Nat.ltb_spec i #|l2|) => //=; cbn in *.
  - rewrite -> app_nth1 by solve_length. done.
  - rewrite -> app_nth2 by solve_length. cbn_length. done.
Qed.

Definition rc_notin_lax_false Γ arg i t :
  check_lax arg = false ->
  rc_notin (Γ ++ [arg]) i t = rc_notin Γ (i + 1) t.
Proof.
  unfold rc_notin, rc_notin_bool. intros lax_arg.
  apply on_free_vars_ext. unfold notin_of_rev_list.
  rewrite -shiftnP_add. eapply shiftnP_ext; intros n.
  rewrite map_app; cbn. rewrite lax_arg.
  rewrite rev_app_distr; cbn. unfold shiftnP.
  destruct n; cbn. 1: reflexivity. rewrite Nat.sub_0_r //.
Qed.

Definition shiftnPneg (k : nat) (p : nat -> bool) (i : nat) :=
  if i <? k then false else p (i - k).

Definition rc_notin_lax_true Γ arg i t :
  check_lax arg = true ->
  rc_notin (Γ ++ [arg]) i t = on_free_vars (shiftnP i (shiftnPneg 1 (notin_of_rev_list (map check_lax Γ)))) t.
Proof.
  unfold rc_notin, rc_notin_bool. intros lax_arg.
  apply on_free_vars_ext.
  unfold notin_of_rev_list.
  eapply shiftnP_ext; intros n.
  rewrite map_app; cbn. rewrite lax_arg.
  rewrite rev_app_distr; cbn.
  destruct n; cbn => //. rewrite Nat.sub_0_r //.
Qed.

Section StrengthArg.
  Context (nb_block : nat).
  Context (up : list (context_decl * bool)).
  Context (nup : context).

  (* remove one arg or update it, and the renaming function  *)
  Definition StrPosArg olb (arg : argument) : Type :=
    (* rc not in arg *)
    rc_notin_argument_bool olb 0 arg *
    (* arg is pos *)
    positive_argument nb_block up nup olb true 0 arg.

  Definition StrAcc := list argument * list argument * (nat -> nat).

  Definition StrPosAcc (acc : StrAcc) : Type :=
      let oargs := acc.1.1 in let nargs := acc.1.2 in let rename_no_rc := acc.2 in
      (* old_args are well-defined *)
      All (fun arg => check_lax arg = false) nargs
      (* nargs are well-defined *)
    * All_telescope (fun Γ => positive_argument nb_block up nup (map check_lax Γ) false 0) nargs
      (* renaming is well-defined *)
    * (forall P i t,
      rc_notin oargs i t ->
      on_free_vars (shiftnP (#|nup| + #|oargs| + i) P) t ->
      on_free_vars (shiftnP (#|nup| + #|nargs| + i) P) ((rename (shiftn i rename_no_rc) t))).

      (* isup_notin up (#|nup| + #|oargs| + i) t ->
      isup_notin up (#|nup| + #|nargs| + i) (rename (shiftn i rename_no_rc) t)). *)

  Definition remove_rc_one (acc : StrAcc) arg :=
    if check_lax arg
    then (acc.1.1 ++ [arg], acc.1.2, strengthen_renaming 1 acc.2)
    else (acc.1.1 ++ [arg], acc.1.2 ++ [rename_argument acc.2 0 arg], shiftn 1 acc.2).

(** t =>>
      ... k + 2 | k + 1 | k -- 0

    unlift 1 k t =>>
      ... (k + 2) - 1 | k -- 0

    lift 1 k (unlift 1 k t) =>>
      ... (k + 2) - 1 + 1 | k -- 0

    t := same term as k + 1 is not in it
*)
  Definition pos_remove_rc_one acc arg :
    StrPosArg (map check_lax acc.1.1) arg ->
    StrPosAcc acc ->
    StrPosAcc (remove_rc_one acc arg).
  Proof.
    intros [rc_notin_arg pos_arg].
    intros [[oargs nargs] pos_rename_no_rc].
    unfold remove_rc_one. destruct (check_lax arg) eqn:lax_arg; cbn in *.
    (* branch true => arg is removed *)
    + repeat split => //.
      cbn_length; cbn. intros P k t rc_notin_t isup_notin_t.
      rewrite rc_notin_lax_true in rc_notin_t => //.
      rewrite -> (unlift_lift 1 k t).
      2: {
        eapply on_free_vars_impl; only 2: apply rc_notin_t.
        eapply shiftnP_impl. unfold shiftnPneg.
        intros i; destruct i; done.
      }
      rewrite shiftn_strengthen.
      eapply (pos_rename_no_rc P).
      (* so tedious *)
      - unfold rc_notin, unlift, rc_notin_bool.
        rewrite on_free_vars_rename.
        unfold shiftnPneg in rc_notin_t. unfold unlift_renaming.
        eapply on_free_vars_impl; only 2 : apply rc_notin_t.
        intros i. unfold shiftnP; cbn.
        destruct (Nat.ltb_spec i k); cbn.
        * assert (i <? k = true) as -> by lia; cbn. done.
        * destruct (Nat.leb_spec (i - k) 0); cbn.
          1: discriminate.
          assert (i - 1 <? k = false) as -> by lia; cbn.
          intros JJ. replace (i - 1 -k) with (i - k - 1) by lia. done.
      - unfold unlift, isup_notin.
        rewrite on_free_vars_rename.
        eapply on_free_vars_impl2; [ | apply rc_notin_t | apply isup_notin_t  ].
        intros j. destruct k; cbn.
        * unfold shiftnPneg. destruct j; cbn.
          1: discriminate.
          intros _. rewrite !Nat.add_0_r Nat.sub_0_r.
          rewrite -shiftnP_add.
          (change j with ((fun (n : nat) => n) j)).
          eapply shiftnP_impl_fct.
          unfold shiftnP; cbn. intros ?; rewrite Nat.sub_0_r //.
        * intros _.
          replace (#|nup| + #|acc.1.1| + 1 + S k) with ((#|nup| + #|acc.1.1|) + (1 + S k)) by lia.
          replace (#|nup| + #|acc.1.1| + S k) with ((#|nup| + #|acc.1.1|) + S k) by lia.
          rewrite -shiftnP_add. rewrite -(shiftnP_add (_ + _) (S k)).
          (change j with ((fun (n : nat) => n) j)).
          eapply shiftnP_impl_fct.
          intros j2. unfold shiftnP, unlift_renaming.
          destruct (Nat.ltb_spec j2 (S k)); cbn.
          1: assert (j2 <=? k = true) as -> by lia; cbn; done.
          destruct (Nat.leb_spec (j2 -1) k); cbn.
          1: done.
          destruct (Nat.leb_spec j2 (S k)); cbn.
          1: lia.
          replace (j2 - S (S k)) with (j2 -1 - S k) by lia.
          done.
    (* branch false => arg is keept *)
    + repeat split; cbn.
      - apply All_app_inv => //. repeat constructor => //.
        rewrite argument_mapi_check_lax //.
      - constructor => //.
        destruct arg; only 2-4: inversion lax_arg.
        cbn. constructor.
        rewrite length_map. apply pos_rename_no_rc.
        * rewrite (rc_notin_argument_bool_free) in rc_notin_arg.
          unfold rc_notin. done.
        * inversion pos_arg. eapply on_free_vars_up_shift; tea. solve_length.
      - cbn_length; cbn. intros P i t rc_notin_t isup_notin_t.
        rewrite shiftn_add.
        replace (#|nup| + #|acc.1.2| + 1 + i) with (#|nup| + #|acc.1.2| + (i + 1)) by lia.
        eapply pos_rename_no_rc.
        * rewrite -(rc_notin_false _ arg) //.
        * eapply on_free_vars_up_shift; tea; lia.
  Qed.

  Definition pos_remove_rc (Γ : list argument) :
    All_telescope (fun Γ => StrPosArg (map check_lax Γ)) Γ ->
    StrPosAcc (fold_left remove_rc_one Γ (@nil argument, @nil argument, (fun n => n))).
  Proof.
    intros H.
    eapply spec_fold_All_check2 with (check := check_lax) (PX := StrPosArg) (PAcc := StrPosAcc); cbn.
    + apply All_telescope_to_All_check. done.
    + repeat split; try constructor. cbn.
      intros. rewrite shiftn_id rename_ren_id. done.
    + intros [[oargs nargs] f] arg. unfold remove_rc_one.
      destruct (check_lax arg); cbn. all:done.
    + intros. apply pos_remove_rc_one; done.
  Qed.

  Definition remove_rc_id_oargs Γ acc :
    (fold_left remove_rc_one Γ acc).1.1 = acc.1.1 ++ Γ.
  Proof.
    revert acc. induction Γ; cbn.
    + intros; rewrite app_nil_r //.
    + intros.
      replace (acc.1.1 ++ a :: Γ) with ((acc.1.1 ++ [a]) ++ Γ) by rewrite -?app_assoc //=.
      unfold remove_rc_one. destruct (check_lax a); cbn; fold remove_rc_one.
      all : rewrite IHΓ //; cbn.
  Qed.

  Definition remove_rc_nargs Γ : list argument :=
    (fold_left remove_rc_one Γ (@nil argument, @nil argument , (fun n => n))).1.2.

  Definition remove_rc_rename Γ : nat -> nat :=
    (fold_left remove_rc_one Γ (@nil argument, @nil argument , (fun n => n))).2.

  (* properties *)
  Definition length_remove_rc Γ acc :
    #|filter (fun t => ~~ check_lax t) Γ| + #|acc.1.2| =
    #|(fold_left remove_rc_one Γ acc).1.2|.
  Proof.
    clear. revert acc.
    unfold remove_rc_one.
    induction Γ as [|a Γ IHΓ]; cbn => //.
    intros [args f]. destruct (check_lax a); cbn.
    rewrite -IHΓ; cbn; cbn_length; cbn. reflexivity.
    rewrite -IHΓ; cbn; cbn_length; cbn. lia.
  Qed.

End StrengthArg.

Definition rename f above : term -> term := rename (shiftn above f).









(* *** Nested to Mutual *** *)
Section NestedToMutualInd.

(* We encounter a nested rec call of g_... in _l...

  The instanciation of the uniform parameters is defined in the context:

      g_uparams ,,, g_nuparams ,,, g_args ,,, g_largs |- inst_uparams_no_rc

  Yet, the indices are defined in the context:

      l_uparams ,,, l_nuparams |- l_indices

  As the uniform and non-uniform parameters must be the same for all mutual
  inductive blocks g_uparams ,,, g_nuparams, we must move l_nuparams to indices.
  Moreover, we must add g_args ,,, g_largs to the indices for the subtitution
  of l_uparams in l_nuparams ,,, l_indices to be well-typed. This gives us:

      g_args ,,, g_largs ,,,  σ(l_nuparams ,,, indices)

  ISSUE => this creates inductive-inductive types!
          => it SHOULD be possible to be finer only add the context really
              needed and stay mutual

  Solution: Remove rec call, i.e. strengthen including subst

    ↓↓g_args ,,, ↓g_largs ,,,  (↓σ)(l_nuparams ,,, indices)

    Either:
      V1: str pos can't be used in the rest of the context (needed anyway) + a polymorphic argument ?
      V2: add by hand it in the pos condition, should work but v1 would be better

    V1 should be true but hard to prove => This uses V2.

    How to make this work => precise conditions ???
    1. ↓↓g_args ,,, ↓g_largs ,,,  (↓σ)(l_nuparams ,,, indices)
      - rc_notin (filter check_lax = false) g_args
      - rc_notin g_largs
      - You need for (↓σ) not add rc => if isup_notin -> rc_notin after
        -> rc_notin llargs / args
    2. Properties must be preserved, should be ok
    3. Args you create still without rc => conditions

    This also forces us to add the arguments but (STRENGTHEN OR NOT ???)

      ↓g_args ,,, ↓g_largs ,,,  (↓σ)(l_nuparams)

    as arguments of the constructors so that they can be refered in indices.

    Note 1 : Fundamentally they are are non uniform parameters,
    they are indices only because parameters must be common to all blocks.
    That would be nice tough, as we wouldn't have to add them everywhere.

    Note 2 : We can not subtitute the intanciation of non-uniform pamareters nor
    indices as otherwise a constructor of the form  `c : nlist (A * A) -> nlist A`
    would become `c : nlist (nat * nat) -> nlist nat` and there would no longer
    be any way to build a term of type `nlist (nat * nat)`.

  *)


  (* 1. ### Info Nesting ### *)

  (* Information Global Inductive Type *)
  Context (nb_g_block : nat).

  Context (g_uparams_b  : list (context_decl * bool)).
  Notation nb_g_uparams := #|g_uparams_b|.
  Definition g_uparams := map fst g_uparams_b.

  Context (g_nuparams : context).
  Notation nb_g_nuparams := #|g_nuparams|.

  (* Context of the nesting *)
  (* arguments already seen *)
  Context (g_args : list argument).
  Notation nb_g_args := #|g_args|.
  Context (pos_g_args :
    All_telescope (fun Γ arg =>
      is_true (rc_notin_argument Γ 0 arg) *
      (* (forall Ht : check_lax arg = false, is_true (rc_notin Γ 0 (strict_to_term arg Ht))) * *)
      positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax Γ) true 0 arg
    )
  g_args).

  (* Argument to the left of nesting  *)
  Context (g_largs : list term).
  Notation nb_g_largs := #|g_largs|.

  Context (pos_g_largs : Alli (isup_notin g_uparams_b) (nb_g_nuparams + nb_g_args) g_largs).
  Context (rc_notin_g_largs : Alli (rc_notin g_args) 0 g_largs).

  (* Information about the inductive type used for nesting *)
  Context (nb_l_block : nat).
  Notation nb_m_block := (nb_g_block + nb_l_block).

  Context (l_uparams_b : list (context_decl * bool)).
  Notation nb_l_uparams  := #|l_uparams_b|.

  Context (l_nuparams : context).
  Notation nb_l_nuparams := #|l_nuparams|.
  Context (pos_l_nuparams : Alli (isup_notin l_uparams_b) 0
                                (terms_of_cxt l_nuparams)).

  (* Instantiation Nesting *)
  Notation nb_old_cxt_sub := (nb_g_nuparams + nb_g_args + nb_g_largs).

  Context (inst_uparams_a : list (list term * argument)).
  Context (spec_inst_uparams_a :
      All2 (fun x y  =>
          let llargs := x.1 in let arg := x.2 in
          let cdecl  := y.1 in let pos := y.2 in
        (* fully applied ensured by typing*)
          (#|llargs| = cdecl_to_arity cdecl)
          (* llargs are free *)
        * Alli (isup_notin g_uparams_b) nb_old_cxt_sub llargs
          (* args are pos lax or strict depending if you can nest or not *)
        * positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args) pos (nb_g_largs + #|llargs|) arg
    ) inst_uparams_a (List.rev l_uparams_b)).

  Context (rc_notin_inst_llargs_args :
    All (fun p => Alli (rc_notin g_args) nb_g_largs p.1
                  * (rc_notin_argument g_args (nb_g_largs + #|p.1|) p.2))
    inst_uparams_a).


  (* ### 2. Spec Not Strength ### *)
  Definition size_inst_uparams : #|inst_uparams_a| = nb_l_uparams.
  Proof.
    cbn_length.
    rewrite -(List.length_rev (l_uparams_b)).
    eapply All2_length; tea.
  Qed.

  (* !!! rev to remove at a point => probably keep reversing eq *)
  Definition fapp_inst_uparams_a : All2 (fun n x => n = #|x.1|)
      (List.rev (uparams_nb_args l_uparams_b)) inst_uparams_a.
  Proof.
    rewrite -List.map_rev -(map_id inst_uparams_a).
    eapply All2_map. eapply All_sym_inv.
    eapply All2_impl; only 1 : apply spec_inst_uparams_a.
    intros [llargs arg] [cdecl pos]; cbn.
    intros [[]]; solve_length.
  Qed.

  Definition positive_inst_llargs :
    All (fun p => Alli (isup_notin g_uparams_b) nb_old_cxt_sub p.1)
        inst_uparams_a.
  Proof.
    clear rc_notin_g_largs rc_notin_inst_llargs_args.
    induction spec_inst_uparams_a; cbn in spec_inst_uparams_a; constructor.
    inversion spec_inst_uparams_a. subst.
    destruct x as [llargs arg], y as [cdecl pos], r as [[fapp pos_llargs] pos_arg]; cbn in * => //.
    apply IHa. assumption.
  Qed.

  Definition positive_true_all :
    All (fun x => positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args)
                      true (nb_g_largs + #|x.1|) x.2) inst_uparams_a.
  Proof.
    clear rc_notin_g_largs rc_notin_inst_llargs_args.
    induction spec_inst_uparams_a; constructor; cbn; eauto.
    destruct x as [llargs arg], y as [cdecl pos], r as [[fapp ?] pos_arg]; cbn in *.
    destruct pos => //. apply positive_argument_increase2 => //.
  Qed.

  Definition inst_to_term_old : (list term * argument) -> term :=
  fun '(llargs, arg) =>
    (it_tLambda llargs (argument_to_term nb_g_block g_uparams_b (nb_old_cxt_sub + #|llargs|) arg)).

  Definition pos_inst_to_term_old :
    All2 (fun x y =>
        y.2 = false -> isup_notin g_uparams_b (nb_old_cxt_sub) (inst_to_term_old x)
    ) inst_uparams_a (List.rev l_uparams_b).
  Proof.
    eapply All2_impl ; [exact spec_inst_uparams_a|].
    intros [llargs arg] [cdecl pos] [[fapp_llargs isup_notin_llargs] pos_arg]; cbn in *.
    destruct pos. 1: intros x; inversion x.
    intros _. unfold inst_to_term_old.
    apply isup_notin_tLambda => //.
    destruct (positive_argument_strict pos_arg) as [t [_ ->]]; cbn.
    inversion pos_arg => //. eapply on_free_vars_up_shift; only 2: tea; solve_length.
  Qed.

  Definition inst_uparams : nat -> term :=
    fun n => nth n (map inst_to_term_old inst_uparams_a) (tRel n).

  Definition pos_inst_uparams : forall n,
    isup_notinP l_uparams_b n ->
    isup_notin g_uparams_b nb_old_cxt_sub (inst_uparams n).
  Proof.
    intros n. unfold isup_notinP, andP, ind_notinP, sp_uparams_notinP.
    intros x%andb_prop; destruct x as [notInd notSpUparams].
    destruct (Nat.lt_ge_cases n nb_l_uparams) as [nleb | nlt].
    - unfold inst_uparams.
      rewrite negb_true_iff in notSpUparams. revert notSpUparams.
      apply (All2_nth (fun x y => y.2 = false -> isup_notin g_uparams_b nb_old_cxt_sub x)).
      1: cbn_length; rewrite size_inst_uparams //.
      apply All2_map_left. apply pos_inst_to_term_old.
    - apply leb_correct in nlt. rewrite nlt in notInd. inversion notInd.
  Qed.

  Definition inst_preserve_isup_notin (k m : nat) t :
    m = nb_old_cxt_sub + k ->
    isup_notin l_uparams_b k t ->
    isup_notin g_uparams_b m t.[up k inst_uparams].
  Proof.
    intros ->; rewrite Nat.add_comm. apply on_free_vars_inst.
    intros n. rewrite <- shiftnP_add. apply on_free_vars_up.
    apply pos_inst_uparams.
  Qed.

  Definition All_inst_isup_notin k m l :
  m = nb_old_cxt_sub + k ->
  All (isup_notin l_uparams_b k) l ->
  All (isup_notin g_uparams_b m) (map (fun t => t.[up k inst_uparams]) l).
  Proof.
    intros ->; intros H; apply All_map, (All_impl H).
    intros; apply inst_preserve_isup_notin => //.
  Qed.

  Definition Alli_inst_isup_notin l k m :
  m = (nb_old_cxt_sub + k) ->
  Alli (isup_notin l_uparams_b) k l ->
  Alli (isup_notin g_uparams_b) m
          (mapi_rec (fun i t => t.[up i inst_uparams]) l k).
  Proof.
    intros ->. intros X; eapply Alli_mapi_rec; tea; cbn.
    intros. apply inst_preserve_isup_notin => //. lia.
  Qed.


  (* 3. ### Strengthen args + rename ### *)

  (* New args + Spec *)
  Definition g_args_no_rc : list argument :=
    remove_rc_nargs g_args.

  Definition pos_g_args_no_rc :
    All_telescope (fun Γ => positive_argument nb_g_block g_uparams_b g_nuparams
      (repeat false #|Γ|) false 0) g_args_no_rc.
  Proof.
    destruct (pos_remove_rc _ _ _ _ pos_g_args) as [[lax_false pos_nargs] pos_rename].
    intros. unfold g_args_no_rc, remove_rc_nargs.
    eapply (All_telescope_impl pos_nargs). intros.
    apply positive_argument_increase2.
  Admitted.

  Definition g_args_no_rc_false :
    Alli (fun i => positive_argument nb_g_block g_uparams_b g_nuparams
      (repeat false i) false 0) 0 g_args_no_rc.
  Proof.
  Admitted.

  Definition length_g_args_no_rc :
    #|filter (fun t => ~~ check_lax t) g_args| = #|g_args_no_rc|.
  Proof.
    unfold g_args_no_rc. rewrite -length_remove_rc; cbn. cbn_length; done.
  Qed.

  Notation nb_g_args_no_rc := (#|g_args_no_rc|).
  Notation nb_new_cxt_sub := (nb_g_nuparams + nb_g_args_no_rc + nb_g_largs).

  (* New renaming + Spec *)
  Definition rename_no_rc : nat -> nat := remove_rc_rename g_args.

  Definition pos_rename_no_rc i t :
    (rc_notin g_args) i t ->
    isup_notin g_uparams_b (nb_g_nuparams + nb_g_args + i) t ->
    isup_notin g_uparams_b (nb_g_nuparams + nb_g_args_no_rc + i)
                                      (rename rename_no_rc i t).
  Proof.
    destruct (pos_remove_rc _ _ _ _ pos_g_args) as [[pos_oargs pos_nargs] pos_rename].
    intros. apply pos_rename; rewrite remove_rc_id_oargs //.
  Qed.

  (* should follow *)
  Definition pos_rename_no_rc_arg lax i arg :
    rc_notin_argument g_args i arg ->
    positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args) lax i arg ->
    positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args_no_rc) lax i
                                      (rename_argument rename_no_rc i arg).
  Proof.
  Admitted.



  (* 4. Update instantiation and properties *)
  Definition g_largs_no_rc : list term :=
    mapi (rename rename_no_rc) g_largs.

  Definition pos_g_largs_no_rc :
    Alli (isup_notin g_uparams_b) (nb_g_nuparams + nb_g_args_no_rc) g_largs_no_rc.
  Proof.
    eapply (Alli_mapi2 rc_notin_g_largs pos_g_largs); cbn.
    apply pos_rename_no_rc.
  Qed.

  Definition l_inst_uparams_no_rc : list (list term * argument) :=
    map (fun ' (llargs, arg) =>
      let llargs' := mapi (fun i => rename rename_no_rc (nb_g_largs + i)) llargs in
      let arg' := rename_argument rename_no_rc (nb_g_largs + #|llargs|) arg in
      (llargs', arg')
      )
    inst_uparams_a.

  Definition size_l_inst_uparams_no_rc : #|l_inst_uparams_no_rc| = nb_l_uparams.
  Proof.
    cbn_length. rewrite -(List.length_rev (l_uparams_b)). eapply All2_length; tea.
  Qed.

  Definition fapp_l_inst_uparams_no_rc : All2 (fun n x => n = #|x.1|)
      (List.rev (uparams_nb_args l_uparams_b)) l_inst_uparams_no_rc.
  Proof.
    rewrite -List.map_rev -(map_id l_inst_uparams_no_rc).
    eapply All2_map. eapply All_sym_inv.
    apply All2_map_left.
    eapply All2_impl; only 1 : apply spec_inst_uparams_a.
    intros [llargs arg] [cdecl pos]; cbn.
    intros [[]]; solve_length.
  Qed.

  Definition positive_inst_llargs_no_rc :
    All (fun p => Alli (isup_notin g_uparams_b) nb_new_cxt_sub p.1)
        l_inst_uparams_no_rc.
  Proof.
    unfold l_inst_uparams_no_rc.
    eapply All_map, (All_impl2 positive_inst_llargs rc_notin_inst_llargs_args).
    intros [llargs arg]; cbn. intros X [Y _].
    eapply (Alli_mapi2 X Y).
    intros. eapply on_free_vars_up_shift.
    2: { apply pos_rename_no_rc => //. eapply on_free_vars_up_shift; tea. lia. }
    lia.
  Qed.

  Definition positive_true_all_no_rc :
    All (fun x => positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args_no_rc)
                      true (nb_g_largs + #|x.1|) x.2) l_inst_uparams_no_rc.
  Proof.
    unfold l_inst_uparams_no_rc.
    eapply All_map. eapply (All_impl2 rc_notin_inst_llargs_args positive_true_all).
    intros [llargs arg]; cbn_length; cbn. intros [_ ?] ?.
    apply pos_rename_no_rc_arg => //.
  Qed.


  (* 5. instantiation *)

  (* should not have renaming as applied to inst_uparams_no_rc *)
  Definition inst_to_term_no_rc : (list term * argument) -> term :=
    fun '(llargs, arg) =>
      (it_tLambda llargs (argument_to_term nb_g_block g_uparams_b (nb_new_cxt_sub + #|llargs|) arg)).

  Definition pos_inst_to_term :
    All2 (fun x y =>
        y.2 = false -> isup_notin g_uparams_b (nb_new_cxt_sub) (inst_to_term_no_rc x)
    ) l_inst_uparams_no_rc (List.rev l_uparams_b).
  Proof.
    unfold l_inst_uparams_no_rc.
    eapply All2_map_left. eapply All2_impl2.
    + apply spec_inst_uparams_a.
    + apply All2_left_triv. 2: rewrite size_inst_uparams; solve_length.
      apply rc_notin_inst_llargs_args.
    + intros [llargs arg] [cdecl pos] [[fapp_llargs isup_notin_llargs] pos_arg]
        [rc_notin_llargs rc_notin_arg] pos_lax. cbn in *. cbn_length.
      apply isup_notin_tLambda => //.
      - eapply (Alli_mapi2 isup_notin_llargs rc_notin_llargs); cbn. intros.
        eapply on_free_vars_up_shift; only 2: apply pos_rename_no_rc => //. lia.
        eapply on_free_vars_up_shift; tea; solve_length.
      - rewrite pos_lax in pos_arg.
        destruct (positive_argument_strict pos_arg) as [t [notin_t ->]]; cbn.
        cbn_length. eapply on_free_vars_up_shift; only 2: apply pos_rename_no_rc.
      * lia.
      * rewrite -rc_notin_argument_free //.
      * eapply on_free_vars_up_shift; tea; solve_length.
  Qed.

  Definition inst_uparams_no_rc : nat -> term :=
    fun n => nth n (map inst_to_term_no_rc l_inst_uparams_no_rc) (tRel n).

  (* check that if n uparams is not positive
     then the instantiation does not contain the variable
  *)
  Definition pos_inst_uparams_no_rc : forall n,
    isup_notinP l_uparams_b n ->
    isup_notin g_uparams_b nb_new_cxt_sub (inst_uparams_no_rc n).
  Proof.
    intros n. unfold isup_notinP, andP, ind_notinP, sp_uparams_notinP.
    intros x%andb_prop; destruct x as [notInd notSpUparams].
    destruct (Nat.lt_ge_cases n nb_l_uparams) as [nleb | nlt].
    - unfold inst_uparams_no_rc.
      rewrite negb_true_iff in notSpUparams. revert notSpUparams.
      apply (All2_nth (fun x y => y.2 = false -> isup_notin g_uparams_b nb_new_cxt_sub x)).
      1: cbn_length; rewrite size_inst_uparams //.
      apply All2_map_left. apply pos_inst_to_term.
    - apply leb_correct in nlt. rewrite nlt in notInd. inversion notInd.
  Qed.

  Definition inst_no_rc_preserve_isup_notin (k m : nat) t :
    m = nb_new_cxt_sub + k ->
    isup_notin l_uparams_b k t ->
    isup_notin g_uparams_b m t.[up k inst_uparams_no_rc].
  Proof.
    intros ->; rewrite Nat.add_comm. apply on_free_vars_inst.
    intros n. rewrite <- shiftnP_add. apply on_free_vars_up.
    apply pos_inst_uparams_no_rc.
  Qed.

  Definition All_inst_no_rc_isup_notin k m l :
  m = nb_new_cxt_sub + k ->
  All (isup_notin l_uparams_b k) l ->
  All (isup_notin g_uparams_b m) (map (fun t => t.[up k inst_uparams_no_rc]) l).
  Proof.
    intros ->; intros H; apply All_map, (All_impl H).
    intros; apply inst_no_rc_preserve_isup_notin => //.
  Qed.

  Definition Alli_inst_no_rc_isup_notin l k m :
  m = (nb_new_cxt_sub + k) ->
  Alli (isup_notin l_uparams_b) k l ->
  Alli (isup_notin g_uparams_b) m
          (mapi_rec (fun i t => t.[up i inst_uparams_no_rc]) l k).
  Proof.
    intros ->. intros X; eapply Alli_mapi_rec; tea; cbn.
    intros. apply inst_no_rc_preserve_isup_notin => //. lia.
  Qed.









  (* New indices are ↓↓g_args ,,, ↓g_largs ,,,  (↓σ)(l_nuparams ,,, indices)
    + positivity *)
  Definition new_indices indices : context :=
    arguments_to_context nb_g_block g_uparams_b (nb_g_uparams + nb_g_nuparams) g_args_no_rc ,,,
    cxt_of_terms g_largs_no_rc ,,,
    List.rev ( mapi (fun i cdecl =>
              let f := inst (up i inst_uparams_no_rc) in
              mkdecl cdecl.(decl_name) (option_map f cdecl.(decl_body))
                  (f cdecl.(decl_type))) (List.rev (l_nuparams ,,, indices))
      ).

  Definition pos_new_indices indices :
    positive_indices l_uparams_b l_nuparams indices ->
    positive_indices g_uparams_b g_nuparams (new_indices indices).
  Proof.
    unfold positive_indices. intros pos_indices.
    unfold new_indices. rewrite !rev_app_distr ?map_app.
      repeat apply Alli_app_inv; cbn_length.
      - unfold arguments_to_context.
        rewrite rev_involutive -(map_mapi _ _ vassAR) map_map /= map_id.
        eapply (Alli_mapi g_args_no_rc_false). intros i x pos_arg.
        destruct (positive_argument_strict pos_arg) as [t [notin_t ->]]; cbn.
        eapply on_free_vars_up_shift; tea. rewrite repeat_length; solve_length.
      - unfold cxt_of_terms.
        rewrite List.rev_involutive map_map /= map_id.
        eapply (Alli_impl pos_g_largs_no_rc) => //.
      - rewrite rev_involutive map_mapi -(mapi_map (fun i t => t.[up i inst_uparams_no_rc])) map_app mapi_app.
        eapply Alli_app_inv; cbn; cbn_length.
        * apply Alli_inst_no_rc_isup_notin => //.
        * eapply (Alli_mapi pos_indices). intros.
          eapply inst_no_rc_preserve_isup_notin => //. lia.
  Qed.


  (* Extra Arguments: g_args ,,, g_largs ,,,  σ(l_nuparams) + Positivity *)
  Definition cstr_extra_args : list argument :=
       g_args
    ++ map arg_is_free g_largs
    ++ map arg_is_free (mapi_rec (fun i t => t.[up i inst_uparams])
        (terms_of_cxt l_nuparams) 0).

  (* Notation nb_extra_args := #|cstr_extra_args|. *)

  (* Definition nb_new_args_unfold : nb_extra_args = nb_g_args + nb_g_largs + nb_l_nuparams.
  Proof.
    solve_length.
  Qed. *)

  Definition pos_cstr_extra_args :
    All_telescope (fun Γ => positive_argument nb_m_block g_uparams_b g_nuparams (map check_lax Γ) true 0) cstr_extra_args.
  Proof.
    eapply All_telescope_impl; only 2: (intros ? ? X; apply pos_arg_inc; exact X).
    unfold cstr_extra_args.
    repeat apply All_telescope_app_inv; cbn.
    + eapply (All_telescope_impl pos_g_args).
      intros Γ t [rc_notin_t isup_notin_t].
      done.
      (* eapply positive_argument_increase1.
      eapply positive_argument_increase2.
      cbn_length => //. *)
    + eapply All_telescope_map.
      - intros ? ? X; apply pos_arg_is_free. cbn_length. exact X.
      - apply All_telescope_to_Alli with
              (P := (fun n (x : term) => isup_notin g_uparams_b n x))
              (n := nb_g_nuparams + nb_g_args) => //.
        (* apply pos_g_largs. *)
    + eapply All_telescope_map.
      - intros ? ? X; apply pos_arg_is_free; cbn_length; exact X.
      - apply All_telescope_to_Alli with
              (P := (fun n (x : term) => isup_notin g_uparams_b (n) x))
              (n := nb_old_cxt_sub).
        eapply Alli_mapi; tea. cbn. intros. apply inst_preserve_isup_notin => //.
  Qed.

  Definition map_xpred0 {A} (l : list A) : map xpred0 l = repeat false #|l|.
  Proof.
    induction l; cbn; f_equal; eauto.
  Qed.

  Definition lax_cstr_extra_args :
    map check_lax cstr_extra_args = repeat false #|cstr_extra_args|.
  Proof.
    unfold cstr_extra_args; cbn_length.
    rewrite !repeat_app !map_app !map_map !map_xpred0; cbn.
    rewrite !app_assoc.
    repeat f_equal => //. 2: solve_length.
    admit.
  Admitted.


  (** Specialization of Arguments
      1. [sub_uparam] that given [forall largs, A_k args] substitute [A_k]
         for its instanciation [λ llargs, arg] that must be given already updated
      2. [specialize_argument] that specialize an argument, calling [sub_uparam]
         to substitute the strictly positive uniform parameters
  *)

  (* Substitute a strictly positive uniform parameter by its instantiation *)
  (* largs, args : already updated arg to sub [forall largs, A_k args]
     llargs, arg : instantiation [λ llargs, arg] to replace A_k,
                   already updated with largs in the context
  *)
  Definition sub_uparam (largs : list term) (args : list term) (llargs : list term) (arg : argument) : argument :=
    match arg with
    | arg_is_free t => arg_is_free (it_tProd largs (mkApps (it_tLambda llargs t) args))
    | arg_is_sp_uparam ll k x =>
        let ll' := mapi (fun i => subst (List.rev args) i) ll in
        let x' := map (subst (List.rev args) #|ll|) x in
        arg_is_sp_uparam (largs ++ ll') k x'
    | arg_is_ind ll pos_indb i_upi =>
        let ll' := mapi (fun i => subst (List.rev args) i) ll in
        let i_upi' := map (subst (List.rev args) #|ll|) i_upi in
        arg_is_ind (largs ++ ll') pos_indb i_upi'
    | arg_is_nested ll ind u inst_up inst_else =>
        let ll' := mapi (fun i => subst (List.rev args) i) ll in
        let inst_up'  := map (fun ' (llargs, arg) =>
            let llargs' := mapi (fun i => subst (List.rev args) (#|ll| + i)) llargs in
            let arg' := subst_argument (List.rev args) (#|ll| + #|llargs|) arg in
            (llargs', arg')
            ) inst_up
          in
        let inst_else' := map (subst (List.rev args) #|ll|) inst_else in
        arg_is_nested (largs ++ ll') ind u inst_up' inst_else'
    end.

  Tactic Notation "solve_sub_uparams_largs" :=
    ( eapply Alli_mapi; only 1: multi_eassumption;
      intros j x; eapply on_free_vars_subst_eq; only 3: (apply All_rev; tea); solve_length).

  Tactic Notation "solve_sub_uparams_args" :=
    ( eapply All_map, All_impl; only 1: multi_eassumption;
      intros x; eapply on_free_vars_subst_eq; only 3: (apply All_rev; tea); solve_length).

  Definition pos_sub_uparams Γ largs args (lax : bool) nb_binders (llargs : list term) (arg : argument)
    (* contet substitution *)
    (rc_notin_largs : Alli (rc_notin_bool Γ) nb_binders largs)
    (pos_largs : Alli (isup_notin g_uparams_b) (nb_g_nuparams + #|Γ| + nb_binders) largs)
    (pos_args  : All  (isup_notin g_uparams_b  (nb_g_nuparams + #|Γ| + nb_binders + #|largs|)) args)
    (* arg to substitute by *)
    (fapp_arg : #|llargs| = #|args|)
    (pos_llargs : Alli (isup_notin g_uparams_b) (nb_g_nuparams + #|Γ| + nb_binders + #|largs|) llargs)
    (rc_notin_args : All (rc_notin_bool Γ (nb_binders + #|largs|)) args)
    (pos_arg : positive_argument nb_m_block g_uparams_b g_nuparams Γ
                  lax (nb_binders + #|largs| + #|llargs|) arg)
    :
    positive_argument nb_m_block g_uparams_b g_nuparams Γ
      lax nb_binders (sub_uparam largs args llargs arg).
  Proof.
    remember (nb_binders + #|largs| + #|llargs|) as p eqn:Heqp.
    induction pos_arg using positive_argument_rect' in Heqp |- *; cbn.
    all: (ltac2:(nconstructor 4)); cbn_length => //; tea;
    try solve [apply Alli_app_inv; mtea; solve_sub_uparams_largs | solve_sub_uparams_args].
    + apply isup_notin_tProd => //.
      apply isup_notin_mkApps => //.
      eapply isup_notin_tLambda_eq; tea; lia.
    + eapply All_map. eapply (All_impl rc_notin_instance); cbn.
      intros [llargs0 arg0]. cbn. intros [rc_notin_llargs0 rc_notin_arg0]; cbn. split.
      * eapply (Alli_mapi rc_notin_llargs0). intros i t rc_notin_t.
        eapply on_free_vars_subst_eq; only 3: apply All_rev; tea; solve_length.
      * cbn_length. eapply on_free_vars_argument_subst_eq; only 3: apply All_rev; tea; solve_length.
    + clear rc_notin_instance.
      induction Ppos_nested; constructor. 2: apply IHPpos_nested.
      destruct x as [l_ll l_arg], y as [cdecl pos_arg], r as [[fapp pos_l_ll] pos_l_arg]; cbn in *.
      cbn_length; repeat split => //.
      * solve_sub_uparams_largs.
      * clear p al Ppos_nested isup_notin_instance IHPpos_nested.
        rewrite Heqp in pos_l_arg.
        eapply pos_subst_argument_eq; tea. 4: apply All_rev; tea.
        all: cbn_length; try reflexivity; lia.
  Qed.

  Definition err_arg : list term * argument
    := ([], arg_is_free (tVar "impossible case")).

  (* Specialize an argument
  1. If it is a strpos uparams => substite by its instantiation
  2. Otherwise propagate the instantiation

  pos sub_cxt : how deep after the sub_contxt => needed to lift the instantiation
    => l_nuparams (becomes arg) + Γ
  *)
  Fixpoint specialize_argument (pos_sub_cxt : nat) (arg : argument) : argument :=
    match arg with
    | arg_is_free t =>
        arg_is_free (t.[up pos_sub_cxt inst_uparams])
    | arg_is_sp_uparam largs k args =>
        (* update largs and args of [forall largs, A_k args] to sub *)
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams]) largs pos_sub_cxt in
        let args'  := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams]) args in
        (* get and lift the instantiation *)
        let ' (llargs, arg_to_sub) := nth k inst_uparams_a err_arg in
        let llargs := map (lift0 (pos_sub_cxt + #|largs|)) llargs in
        let arg_to_sub := lift_argument (pos_sub_cxt + #|largs|) #|llargs| arg_to_sub in
        sub_uparam largs' args' llargs arg_to_sub
    | arg_is_ind largs i inst_uparams_indices =>
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams]) largs pos_sub_cxt in
        (* we need to add var for new nup + new indices - old_nup *)
        (* TO CHANGE TO USE NOT NEW *)
        let new_indices := tRels (pos_sub_cxt + #|largs|) (nb_g_nuparams + nb_g_args + #|g_largs|) in
        (* nup are now indices so just need to be updated *)
        let inst_uparams_indices'  := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams]) inst_uparams_indices in
        arg_is_ind largs' (i + nb_g_block) (new_indices ++ inst_uparams_indices')
    | arg_is_nested largs ind u insta_uparams inst_nuparams_indices =>
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams]) largs pos_sub_cxt in
        let insta_uparams'  := map (fun ' (llargs, arg) =>
            let llargs' := mapi_rec (fun i t => t.[up i inst_uparams]) llargs (pos_sub_cxt + #|largs|) in
            let arg' := specialize_argument (pos_sub_cxt + #|largs| + #|llargs|) arg in
            (llargs', arg')
            ) insta_uparams
          in
        let inst_nuparams_indices' := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams]) inst_nuparams_indices in
        arg_is_nested largs' ind u insta_uparams' inst_nuparams_indices'
    end.


  Definition check_lax_specialize_argument Γ i:
    All2 (fun a b => is_true (~~ a) -> is_true (~~ b))
    (map check_lax Γ) (map check_lax (mapi_rec specialize_argument Γ i)).
  Proof.
    induction Γ in i |- *; cbn; constructor; eauto.
    destruct a; cbn. all: solve [done | intros [=]].
  Qed.

  Definition pos_specialize_argument Γ lax nb_binders arg :
    positive_argument nb_l_block l_uparams_b l_nuparams (map check_lax Γ) lax nb_binders arg ->
    positive_argument nb_m_block g_uparams_b g_nuparams
      (map check_lax (cstr_extra_args ++ (mapi_rec specialize_argument Γ nb_l_nuparams)))
      lax nb_binders (specialize_argument (nb_l_nuparams + #|Γ| + nb_binders) arg).
  Proof.
    intro pos_arg; induction pos_arg using positive_argument_rect'; cbn.
    + apply pos_arg_is_free; rewrite -> ? length_map in *.
      apply inst_preserve_isup_notin => //. cbn_length. lia.
    + rewrite <- Nat.add_assoc.
      destruct (nth k inst_uparams_a err_arg) as [llargs arg_to_sub] eqn:H.
      apply eq_prod in H as [Hfst Hsnd]. cbn_length.
      apply pos_sub_uparams. all: cbn_length; rewrite -> ? length_map in *.
      - eapply (Alli_mapi_rec rc_notin_largs); cbn. intros i t rc_notin_t.
        rewrite map_app lax_cstr_extra_args. apply rc_notin_false_left1.
        eapply (rc_notin_decrease (check_lax_specialize_argument Γ _)).
        admit.
      - apply Alli_inst_isup_notin => //. lia.
      - apply All_inst_isup_notin => //. lia.
      - rewrite - fapp -Hfst. symmetry.
        apply (All2_nth (fun n x => n = #|x.1|)); only 1: solve_length.
        apply fapp_inst_uparams_a.
      - eapply Alli_map. eapply Alli_impl.
        * rewrite -Hfst. apply All_nth => //. 1: rewrite size_inst_uparams; lia.
          apply positive_inst_llargs.
        * intros n x H.
          replace (nb_old_cxt_sub + nb_l_nuparams + #|Γ| + nb_binders + #|largs| + n)
          with ((nb_l_nuparams + #|Γ| + nb_binders + #|largs|) + (nb_old_cxt_sub + n))
          by lia.
          unfold isup_notin.
          rewrite -shiftnP_add.
          rewrite -{1}(Nat.add_0_r (nb_l_nuparams + #|Γ| + nb_binders + #|largs|)).
          apply on_free_vars_lift_impl. rewrite shiftnP_add; cbn. exact H.
      - apply All_map, (All_impl rc_notin_args). intros t rc_notin_t.
        rewrite map_app lax_cstr_extra_args. apply rc_notin_false_left1.
        eapply (rc_notin_decrease (check_lax_specialize_argument Γ _)).
        admit.
      - apply pos_arg_inc => //.
        assert (positive_argument nb_g_block g_uparams_b g_nuparams (map check_lax g_args) lax (nb_g_largs + #|llargs|) arg_to_sub).
        1: { rewrite -Hfst -Hsnd. apply All_nth => //. 1: rewrite size_inst_uparams; lia.
             destruct lax; only 2: inversion e. apply positive_true_all.
          }
        eapply @pos_lift_argument_eq with
          (Γ1 := (map check_lax (g_args ++ map arg_is_free g_largs)))
          (nb_binders := 0) (n := nb_binders + #|largs|).
        * reflexivity.
        * rewrite !map_app -!app_assoc. reflexivity.
        * lia.
        * solve_length.
        * rewrite !map_app. rewrite map_map map_xpred0.
          eapply pos_arg_notin_unfold => //.
    + apply pos_arg_is_ind => //; rewrite -> ? length_map in *.
      - lia.
      - apply Alli_inst_isup_notin => //. solve_length.
      - apply All_app_inv; cbn_length.
        -- unfold tRels. apply All_rev_pointwise_map. cbn.
           intros. apply shiftnP_lt. lia.
        -- apply All_inst_isup_notin => //. lia.
    + apply pos_arg_is_nested with (mdecl := mdecl); rewrite -> ? length_map in * => //.
      - apply Alli_inst_isup_notin => //. solve_length.
      - apply All_inst_isup_notin => //. solve_length.
      - eapply (Alli_mapi_rec rc_notin_largs). intros i t rc_notin_t.
        admit.
      - apply All_map, (All_impl rc_notin_instance).
        intros [llargs arg] [rc_notin_llargs rc_notin_arg]; cbn; cbn_length; split.
        (* induction or sth ??? *)
        all: admit.
      - induction Ppos_nested; rewrite -> ? length_map in * ; constructor; only 2: apply IHPpos_nested.
        destruct x as [l_ll l_arg], y as [cdecl pos_arg], r as [[fapp pos_l_ll] pos_l_arg]; cbn in *.
        cbn_length; repeat split => //.
        * apply Alli_inst_isup_notin => //. lia.
        * apply_eq p. f_equal. lia.
  Admitted.

  (* The instanciation of the uniform parameters is defined in the context:

        g_uparams ,,, g_nuparams ,,, g_args ,,, g_largs |- inst_uparams

     The constructor are definied in the context

        l_uparams ,,, l_nuparams ,,, cstr_args |- cstr_indices

      We then have as a new type:

         (↓↓g_args ,,, ↓g_largs), (↓σ)(l_nuparams ,,, cstr_args)
          |- new_indices ++ (↓σ) #|l_nuparams ,,, cstr_args| cstr_indices

      Note, we must also add references to new_indices as
      (↓↓g_args ,,, ↓g_largs), (↓σ)(l_nuparams) are new  indices!
  *)
  Definition specialize_ctor (ctor : constructor_body) : constructor_body :=
  {|
    cstr_name     := todo;
    cstr_args    := cstr_extra_args
                    ++ mapi (fun i => specialize_argument (nb_l_nuparams + i)) ctor.(cstr_args)  ;
    cstr_indices :=    tRels #|ctor.(cstr_args)| (#|g_args_no_rc| + #|g_largs| + #|l_nuparams|)
                    ++ map (inst (up (nb_l_nuparams + #|ctor.(cstr_args)|) inst_uparams_no_rc))
                           ctor.(cstr_indices)
  |}.

  Definition pos_specialize_ctor ctor :
    positive_constructor nb_l_block l_uparams_b l_nuparams ctor ->
    positive_constructor nb_m_block g_uparams_b g_nuparams (specialize_ctor ctor).
  Proof.
    unfold positive_constructor, specialize_ctor. cbn [cstr_args cstr_indices].
    intros [pos_cstr_args pos_cstr_indices]. split.
    (* pos args *)
    + apply All_telescope_app_inv.
      - admit.
      (* apply pos_cstr_extra_args. *)
      - admit.
        (* clear pos_cstr_indices.
        induction pos_cstr_args; cbn. 1: constructor.
        rewrite mapi_app. apply All_telescope_app_inv.
        * apply IHpos_cstr_args => //.
        * cbn. apply All_telescope_singleton.
          unfold mapi. rewrite -mapi_rec_add. fold specialize_argument.
          rewrite {1}Nat.add_0_r app_nil_r Nat.add_assoc.
          apply pos_specialize_argument with (Γ := Γ).
          assumption. *)
    + cbn_length. apply All_app_inv.
      (* need to change indices for it to work *)
      - unfold tRels. apply All_rev_pointwise_map; cbn.
        intros. apply shiftnP_lt. cbn_length.
        admit.
        (* lia. *)
      (* - apply All_inst_no_rc_isup_notin; tea. lia. *)
  Admitted.

  Definition specialize_one_inductive_body (idecl : one_inductive_body) : one_inductive_body :=
  {|
    ind_name      := todo;
    ind_indices   := new_indices idecl.(ind_indices);
    ind_sort      := todo;
    ind_kelim     := todo;
    ind_ctors     := map specialize_ctor idecl.(ind_ctors);
    ind_relevance := todo;
  |}.

  Definition pos_specialize_idecl idecl :
    positive_one_inductive_body nb_l_block l_uparams_b l_nuparams idecl ->
    positive_one_inductive_body nb_m_block g_uparams_b g_nuparams (specialize_one_inductive_body idecl).
  Proof.
    intros [pos_ctors pos_indices]; split; cbn.
    + eapply All_map, (All_impl pos_ctors pos_specialize_ctor).
    (* one extra case if you want to prove it is not inductiv inductive *)
    + apply pos_new_indices => //.
  Qed.

End NestedToMutualInd.











(* Going From Nested to Mutual *)

(* Env + View is correct *)
Axiom (E_pos : forall kname, if lookup_minductive E kname is Some mdecl
                             then positive_mutual_inductive_body (mutual_to_view mdecl)
                             else False).


Section NestedToMutualIndb.

  Context (nb_g_block : nat).
  Context (g_uparams_b : list (context_decl * bool)).
  Notation nb_g_uparams := #|g_uparams_b|.

  Context (g_nuparams : context).
  Notation nb_g_nuparams := #|g_nuparams|.

  (* function to be folded *)
  Definition Acc : Type := list argument * list one_inductive_body.

  Definition nested_to_mutual_one_argument (acc : Acc) (arg : argument) : Acc :=
    let nargs := acc.1 in let acc_indb := acc.2 in
    match arg with
    | arg_is_nested largs (mkInd kname pos_indb) u inst_uparams_no_rc inst_nuparams_indices =>
      if option_map mutual_to_view (lookup_minductive E kname) is Some mdecl
      then (let new_indb := map (specialize_one_inductive_body (nb_g_block + #|acc_indb|)
                                  g_uparams_b g_nuparams nargs largs mdecl.(ind_nuparams)
                                  inst_uparams_no_rc) mdecl.(ind_bodies) in
            (* we need to add var for new nup + new indices => dup *)
            let new_indices := tRels 0 nb_g_nuparams
              ++ filter2 (map check_lax nargs) (tRels nb_g_nuparams #|nargs|)
              ++ tRels (nb_g_nuparams + #|nargs|) #|largs| in
          let new_arg := arg_is_ind largs (pos_indb + nb_g_block + #|acc_indb|)
                          (new_indices ++ inst_nuparams_indices) in
          (nargs ++ [new_arg], acc_indb ++ new_indb))
      else (nargs ++ [arg], acc_indb)
    | _ => (nargs ++ [arg], acc_indb)
    end.

  (* Fold Arguments *)
  Definition PosArgBool lb arg :=
    rc_notin_argument_bool lb 0 arg *
    positive_argument nb_g_block g_uparams_b g_nuparams lb true 0 arg.

  Definition PosArg Γ (arg : argument) : Type :=
    PosArgBool (map check_lax Γ) arg.

  Definition PosAcc (acc : Acc) : Type :=
      let nargs := acc.1 in let acc_indb := acc.2 in
        All_telescope (fun Γ arg =>
          is_true (rc_notin_argument Γ 0 arg) *
          positive_argument (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams (map check_lax Γ) true 0 arg
        ) nargs
    * (All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb).

  Tactic Notation "solve_nested_to_mut" :=
    split => //; apply All_telescope_app_inv => //; repeat constructor => //;
    apply All_telescope_singleton; rewrite app_nil_r; split => //; constructor => //; lia.

  Definition pos_nested_to_mutual_one_argument (acc : Acc) arg :
    (* spec *)
    forall (pos_acc : PosAcc acc) (pos_arg : PosArg acc.1 arg),
    (* res *)
    PosAcc (nested_to_mutual_one_argument acc arg).
  Proof.
    destruct acc as [nargs acc_indb].
    unfold PosAcc, PosArg.
    intros [pos_nargs pos_acc_indb] [rc_notin_arg pos_arg].
    destruct pos_arg; cbn in *.
    all: try solve_nested_to_mut.
    rewrite -> ? Nat.add_0_r in *.
    rewrite -> ? length_map in *.
    rewrite e0; cbn in *. cbn_length.
    pose proof (p := E_pos kname); rewrite e0 in p; cbn in p.
    destruct p as [pos_l_nuparams pos_l_indb]. split; cbn.
    + apply All_telescope_app_inv.
      1 :{ eapply All_telescope_impl; tea; cbn.
           intros Γ myarg [rc_notin_myarg pos_myarg]. split => //. apply pos_arg_inc => //. }
      apply All_telescope_singleton. rewrite app_nil_r. split => //.
      - admit.
      - constructor; cbn_length => //.
        1: { rewrite -mutual_to_view_ind. lia. }
        apply All_app_inv => //. repeat apply All_app_inv.
        * apply All_rev_pointwise_map; intros; apply shiftnP_lt; lia.
        * apply All_filter2, All_rev_pointwise_map; intros; apply shiftnP_lt; lia.
        * apply All_rev_pointwise_map; intros; apply shiftnP_lt; lia.
    + apply All_app_inv; only 1: (eapply All_impl; tea; intros; apply pos_idecl_inc) => //.
      eapply All_map, (All_impl pos_l_indb), pos_specialize_idecl => //.
      eapply All2_impl; only 1: rewrite -mutual_to_view_uparams; tea.
      intros [llargs arg] [cdecl pos] [[fapp pos_llargs] pos_arg].
      cbn in *. repeat split; tea. apply pos_arg_inc => //.
  Admitted.

  Definition length1_nested_to_mutual_one_argument acc arg :
    #|(nested_to_mutual_one_argument acc arg).1| = 1 + #|acc.1|.
  Proof.
    destruct arg; cbn.
    4: destruct ind; destruct (lookup_minductive E _).
    all: cbn_length; cbn; try lia.
  Qed.

  Definition nested_to_mutual_argument args acc_indb :=
    fold_left nested_to_mutual_one_argument args ([],acc_indb).

  Definition length_pos_left args acc :
    #|(fold_left nested_to_mutual_one_argument args acc).1| = #|acc.1| + #|args|.
  Proof.
    induction args in acc |- *; cbn.
    - lia.
    - rewrite IHargs. rewrite length1_nested_to_mutual_one_argument. lia.
  Qed.



  (* ccl fold *)
  Definition pos_nested_to_mutual_argument {args acc_indb}
    (* spec *)
    (pos_args : All_telescope PosArg args)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb) :
    (* new_spec *)
    PosAcc (nested_to_mutual_argument args acc_indb).
  Proof.
    unfold nested_to_mutual_argument.
    eapply (spec_fold_All_check check_lax _ _ _ PosAcc PosArgBool); cbn.
    - apply All_telescope_to_All_check. done.
    - repeat constructor; cbn => //.
    - clear. intros [acc_nargs acc_indb] arg.
      destruct arg; cbn. 4: destruct ind as [kname pos_indb], (lookup_minductive E kname).
      all:rewrite ? map_app; cbn; reflexivity.
    - apply pos_nested_to_mutual_one_argument.
  Qed.


  Definition nested_to_mutual_one_ctor ctor acc_indb :
    constructor_body * list one_inductive_body :=
  let x := nested_to_mutual_argument ctor.(cstr_args) acc_indb in
  let new_ctor := {|
    cstr_name    := ctor.(cstr_name);
    cstr_args    := x.1 ;
    cstr_indices := ctor.(cstr_indices)
    |} in
  (new_ctor, x.2).

  Definition pos_nested_to_mutual_one_ctor ctor acc_indb
    (* spec *)
    (pos_ctor : positive_constructor nb_g_block g_uparams_b g_nuparams ctor)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb):
    (* new_spec *)
    let x := nested_to_mutual_one_ctor ctor acc_indb in
      (positive_constructor (nb_g_block + #|x.2|) g_uparams_b g_nuparams x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2).
  Proof.
    destruct pos_ctor as [pos_args pos_indices].
    pose proof (e := pos_nested_to_mutual_argument pos_args pos_acc_indb).
    destruct e as [pos_nargs pos_nacc].
    cbn. set (x := nested_to_mutual_argument ctor.(cstr_args) acc_indb) in *.
    repeat split; cbn => //.
    rewrite length_pos_left => //.
  Qed.


  Definition nested_to_mutual_ctor ctors acc_indb : list constructor_body * list one_inductive_body :=
  fold_left ( fun acc ctor =>
      let x := nested_to_mutual_one_ctor ctor acc.2 in
      (acc.1 ++ [x.1], x.2)
    )
    ctors
    ([],acc_indb).

  Definition Alli_cst {A} (P : A -> Type) (l : list A) k :
    All P l -> Alli (fun _ => P) k l.
  Proof.
    intros X; induction X in k |- *; constructor; eauto.
  Qed.

  Definition length2_nested_to_mutual_argument args new_indb :
    #|new_indb| <= #|(nested_to_mutual_argument args new_indb).2|.
  Proof.
    unfold nested_to_mutual_argument.
    change new_indb with (( @nil argument,new_indb).2) at 1.
    generalize (( @nil argument, new_indb)).
    induction args as [|arg args IHargs]; cbn.
    - lia.
    - intros. etransitivity. 2: eapply IHargs.
      destruct arg; cbn.
      4: destruct ind as [kname ?]; cbn; destruct (lookup_minductive E kname); cbn.
      all : try lia.
      solve_length.
  Qed.


  Definition pos_nested_to_mutual_ctors {ctors acc_indb}
    (* spec *)
    (pos_ctors : All (positive_constructor nb_g_block g_uparams_b g_nuparams) ctors)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb) :
    (* new_spec *)
    let x := nested_to_mutual_ctor ctors acc_indb in
      (All (positive_constructor (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2).
  Proof.
    cbn. unfold nested_to_mutual_ctor.
    eapply spec_fold_Alli; cbn.
    - apply Alli_cst. tea.
    - split; [constructor| assumption].
    - intros; cbn_length ; cbn ; lia.
    - intros [nctors new_indb] ctor; cbn.
      intros [pos_nctors pos_new_indb] pos_ctor.
      split.
      + apply All_app_inv.
        * eapply All_impl; tea.
          intros; eapply pos_ctor_inc_le; tea.
          apply add_le_mono_l_proj_l2r, length2_nested_to_mutual_argument.
        * constructor; only 2: constructor.
          eapply fst.
          eapply pos_nested_to_mutual_one_ctor; cbn => //.
      + eapply snd. apply pos_nested_to_mutual_one_ctor => //.
  Qed.

  Definition length2_nested_to_mutual_ctor ctors new_indb :
    #|new_indb| <= #|(nested_to_mutual_ctor ctors new_indb).2|.
  Proof.
    unfold nested_to_mutual_ctor.
    change new_indb with (( @nil constructor_body,new_indb).2) at 1.
    generalize (( @nil constructor_body, new_indb)).
    induction ctors as [|ctor ctors IHctors]; cbn.
    - lia.
    - intros. etransitivity. 2: eapply IHctors. cbn.
      apply length2_nested_to_mutual_argument.
  Qed.


  (* check preservation *)
  Definition nested_to_mutual_one_indb indb acc_indb : one_inductive_body * list one_inductive_body :=
  let x := nested_to_mutual_ctor indb.(ind_ctors) acc_indb in
  let new_indb := {|
    ind_name      := indb.(ind_name);
    ind_indices   := indb.(ind_indices);
    ind_sort      := indb.(ind_sort);
    ind_kelim     := todo; (* what to do here ? *)
    ind_ctors     := x.1 ;
    ind_relevance := todo; (* what to do here ? *)
  |} in
  (new_indb, x.2).

  Definition pos_nested_to_mutual_one_indb indb acc_indb
    (* spec *)
    (pos_indb : positive_one_inductive_body nb_g_block g_uparams_b g_nuparams indb)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb):
    (* new_spec *)
    let x := nested_to_mutual_one_indb indb acc_indb in
      (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2).
  Proof.
    destruct pos_indb as [pos_ctors pos_indices]; cbn.
    pose proof (e := pos_nested_to_mutual_ctors pos_ctors pos_acc_indb).
    destruct e as [pos_nctros pos_nacc].
    cbn in *. set (x := nested_to_mutual_one_indb indb acc_indb) in *.
    repeat split; cbn => //.
  Qed.


  Definition nested_to_mutual_indb indbs : list one_inductive_body * list one_inductive_body :=
    fold_left ( fun acc indb =>
      let x := nested_to_mutual_one_indb indb acc.2 in
      (acc.1 ++ [x.1], x.2)
      )
      indbs
      ([],[]).

  Definition pos_nested_to_mutual_indb {indbs}
    (* spec *)
    (pos_indbs : All (positive_one_inductive_body nb_g_block g_uparams_b g_nuparams) indbs):
    (* new_spec *)
    (fun x =>
      (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.1)
    * (All (positive_one_inductive_body (nb_g_block + #|x.2|) g_uparams_b g_nuparams) x.2))
    (nested_to_mutual_indb indbs).
  Proof.
    cbn. unfold nested_to_mutual_indb.
    eapply spec_fold_Alli; cbn.
    - apply Alli_cst. tea.
    - rewrite Nat.add_0_r. split; constructor.
    - intros; cbn_length ; cbn ; lia.
    - intros [nindb new_indb] indb; cbn.
      intros [pos_nindb pos_new_indb] pos_indb.
      split.
      + apply All_app_inv.
        * eapply All_impl; tea.
          intros; eapply pos_idecl_inc_le; tea.
          apply add_le_mono_l_proj_l2r, length2_nested_to_mutual_ctor.
        * constructor; only 2: constructor.
          eapply fst.
          eapply pos_nested_to_mutual_one_indb; cbn => //.
      + eapply snd. apply pos_nested_to_mutual_one_indb => //.
  Qed.


  Definition length_nested_to_mutual_indb indbs :
    #|(nested_to_mutual_indb indbs).1| = #|indbs|.
  Proof.
    unfold nested_to_mutual_indb; cbn.
    rewrite -(Nat.add_0_r #|indbs|).
    change 0 with #|( @nil one_inductive_body, @nil one_inductive_body).1|.
    generalize ( @nil one_inductive_body, @nil one_inductive_body).
    induction indbs; cbn.
    - lia.
    - intros p. rewrite IHindbs. cbn_length; cbn. lia.
  Qed.

End NestedToMutualIndb.


Definition nested_to_mutual (mdecl : mutual_inductive_body) : mutual_inductive_body :=
  {|
    ind_finite    := mdecl.(ind_finite);
    ind_uparams   := mdecl.(ind_uparams);
    ind_nuparams  := mdecl.(ind_nuparams);
    ind_bodies    := let x := nested_to_mutual_indb #|mdecl.(ind_bodies)|
                        mdecl.(ind_uparams) mdecl.(ind_nuparams) mdecl.(ind_bodies)
                      in
                      x.1 ++ x.2;
    ind_universes := todo; (* what to do here ? *)
    ind_variance  := todo; (* what to do here ? *)
  |}.

Definition pos_nested_to_mutual mdecl :
  positive_mutual_inductive_body mdecl ->
  positive_mutual_inductive_body (nested_to_mutual mdecl).
Proof.
  intros [pos_mdecl_nuparams pos_mdecl_indb].
  apply (pos_nested_to_mutual_indb) in pos_mdecl_indb as [pos_new_indb pos_acc_indb].
  unfold nested_to_mutual; cbn.
  set (x := nested_to_mutual_indb #|mdecl.(ind_bodies)| mdecl.(ind_uparams)
              mdecl.(ind_nuparams) mdecl.(ind_bodies)) in *.
  (* proof *)
  split; cbn => //.
  cbn_length. rewrite length_nested_to_mutual_indb. apply All_app_inv => //.
Qed.