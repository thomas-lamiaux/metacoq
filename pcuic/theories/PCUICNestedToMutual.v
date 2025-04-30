(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
(* From MetaRocq.Common Require Import BasicAst Primitive Universes Environment. *)
(* From Equations.Prop Require Import Classes EqDecInstances. *)
(* From Coq Require Import List. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv.
Import PCUICEnvironment.
From MetaRocq.PCUIC Require Import PCUICAuxToMove PCUICViewInductive.
Import ViewInductive.


(* Todo list:

[ ] 1. Specialize inductive block
    [X] 1.1 all but nested case
    [ ] 1.2 nested case
    [ ] 1.3 indices
[ ] 2. Proof positivity is preserved
    [X] 2.1 all but nested case
    [ ] 2.2 nested case
    [ ] 2.3 indices
[X] 3. Nested to Mutual
[X] 4. Positivity is preserved

Indices :
=> restrict args pos strict (i.e. no rec call)
=> suppose it, either add it to pos or prove it
=> proof should be the same except instantion to modify
  for strengthening + proof it is "pos"

*)


(* *** Nested to Mutual *** *)

Section NestedToMutualInd.

  (*** Information Global Inductive Type ***)
  Context (nb_g_block : nat).

  (* Context of the nesting *)
    (* uniform parameters *)
    Context (g_uparams_b  : list (context_decl * bool)).
    Notation nb_g_uparams := #|g_uparams_b|.
    Definition g_uparams := map fst g_uparams_b.

    (* non-uniform parameters *)
    Context (g_nuparams : context).
    Notation nb_g_nuparams := #|g_nuparams|.

    (* parameters *)
    Definition g_params : context := g_uparams ,,, g_nuparams.
    Notation nb_g_params := (nb_g_uparams + nb_g_nuparams).

    (* arguments already seen *)
    Context (g_args_a : list argument).
    Notation nb_g_args := #|g_args_a|.

    Definition g_args : context :=
      cxt_of_terms (map (argument_to_term nb_g_block #|g_params|) g_args_a).

    Context (pos_g_args_a : Alli (positive_argument nb_g_block g_uparams_b true) nb_g_nuparams g_args_a).

    (* Argument to the left of nesting  *)
    Context (g_largs_t : list term).
    Notation nb_g_largs := #|g_largs_t|.

    Definition g_largs : context := cxt_of_terms (g_largs_t).

    Context (pos_g_largs_t : Alli (ind_sp_uparams_notin g_uparams_b) (nb_g_nuparams + nb_g_args) g_largs_t).


  (*** Information about the inductive type used for nesting ***)

  Context (nb_l_block : nat).

  Notation nb_m_block := (nb_g_block + nb_l_block).

  (* uparams *)
  Context (l_uparams_b : list (context_decl * bool)).
  Notation nb_l_uparams  := #|l_uparams_b|.

  Definition l_uparams : context := map fst l_uparams_b.

  (* nuparams *)
  Context (l_nuparams : context).
  Notation nb_l_nuparams := #|l_nuparams|.

  Definition l_nuparams_t : list term := terms_of_cxt l_nuparams.

  Context (pos_l_nuparams : Alli (ind_sp_uparams_notin l_uparams_b) 0
    (terms_of_cxt l_nuparams)).

  (* parameters *)
  Definition l_params : context := l_uparams ,,, l_nuparams.
  Notation nb_l_params := (nb_l_uparams + nb_l_nuparams).




  (* instantiation turn to a list of terms *)
  Notation nb_cxt_sub := (nb_g_nuparams + nb_g_args + nb_g_largs).

  Context (inst_uparams_a : list (list term * argument)).

  Context (spec_inst_uparams_a :
      All2 (fun x y  =>
          let llargs := x.1 in let arg := x.2 in
          let cdecl  := y.1 in let pos := y.2 in
        (* fully applied ensured by typing*)
          (#|llargs| = cdecl_to_arity cdecl)
          (* llargs are free *)
        * Alli (ind_sp_uparams_notin g_uparams_b) nb_cxt_sub llargs
          (* args are pos lax or strict depending if you can nest or not *)
        * positive_argument nb_g_block g_uparams_b pos (nb_cxt_sub + #|llargs|) arg
    ) inst_uparams_a (rev l_uparams_b)).

  Definition size_inst_uparams : #|inst_uparams_a| = nb_l_uparams.
  Proof.
    rewrite -(length_rev (l := l_uparams_b)).
    eapply All2_length; tea.
  Qed.

  Definition All_sym_inv : forall {A B C : Type} (f : A -> C) (g : B -> C)
    l l',
    All2 (fun y x => f x = g y) l' l ->
    All2 (fun x y => f x = g y) l  l'.
  Proof.
    intros * X; induction X; constructor; eauto.
  Qed.

  Definition fapp_inst_uparams : All2 (fun n x => n = #|x.1|)
      (rev (uparams_nb_args l_uparams_b)) inst_uparams_a.
  Proof.
    rewrite -map_rev -(map_id inst_uparams_a).
    eapply All2_map. eapply All_sym_inv.
    eapply All2_impl; only 1 : apply spec_inst_uparams_a.
    intros [llargs arg] [cdecl pos]; cbn.
    intros []; now symmetry.
  Qed.

  (* awfull !!! *)
  Definition positive_inst_llargs :
    All (fun p => Alli (ind_sp_uparams_notin g_uparams_b) nb_cxt_sub p.1) inst_uparams_a.
  Proof.
    induction spec_inst_uparams_a; cbn in spec_inst_uparams_a; constructor. inversion spec_inst_uparams_a. subst.
    destruct x, y; cbn in *. destruct r as [ []]. assumption.
    apply IHa. assumption.
  Qed.

  Definition inst_to_term : (list term * argument) -> term :=
    fun '(llargs, arg) => it_tLambda llargs (argument_to_term nb_g_block (nb_cxt_sub + #|llargs|) arg).

  Definition pos_inst_to_term :
    All2 (fun ' (llargs, arg) ' (cdecl, pos) =>
        pos = false -> ind_sp_uparams_notin g_uparams_b (nb_cxt_sub) (inst_to_term (llargs, arg))
    ) inst_uparams_a (rev l_uparams_b).
  Proof.
    eapply All2_impl ; [exact spec_inst_uparams_a|].
    intros [llargs arg] [cdecl pos] [[fapp_llargs notin_llargs] pos_arg]; cbn in *.
    destruct pos. 1: intros x; inversion x.
    intros _. unfold inst_to_term.
    apply ind_sp_uparams_notin_tLambda => //.
    destruct (positive_argument_strict _ _ pos_arg) as [t ->]; cbn.
    inversion pos_arg => //.
  Qed.

  Definition inst_uparams : nat -> term :=
    fun n => nth n (map inst_to_term inst_uparams_a) (tRel n).

  (* check that if n uparams is not positive
     then the instantiation does not contain the variable
  *)
  Definition pos_inst_uparams : forall n,
    ind_sp_uparams_notinP l_uparams_b n ->
    ind_sp_uparams_notin g_uparams_b nb_cxt_sub (inst_uparams n).
  Proof.
    intros n. unfold ind_sp_uparams_notinP, andP, ind_notinP, sp_uparams_notinP.
    intros x%andb_prop; destruct x as [notInd notSpUparams].
    destruct (Nat.lt_ge_cases n nb_l_uparams) as [nleb | nlt].
    - unfold inst_uparams.
      rewrite negb_true_iff in notSpUparams. revert notSpUparams.
      apply (All2_nth (fun x y => y.2 = false -> ind_sp_uparams_notin g_uparams_b nb_cxt_sub x)).
      1: cbn_length; rewrite size_inst_uparams //.
      rewrite -(map_id (rev l_uparams_b)).
      apply All2_map. eapply All2_impl. 1: apply pos_inst_to_term.
      now intros [] [].
    - apply leb_correct in nlt. rewrite nlt in notInd. inversion notInd.
  Qed.

  Definition inst_preserve_not (k : nat) t :
    ind_sp_uparams_notin l_uparams_b k t ->
    ind_sp_uparams_notin g_uparams_b (nb_cxt_sub + k) t.[up k inst_uparams].
  Proof.
    rewrite Nat.add_comm. apply on_free_vars_inst.
    intros n. rewrite <- shiftnP_add. apply on_free_vars_up.
    apply pos_inst_uparams.
  Qed.

  Definition inst_preserve_not_eq (k m : nat) t :
    m = nb_cxt_sub + k ->
    ind_sp_uparams_notin l_uparams_b k t ->
    ind_sp_uparams_notin g_uparams_b m t.[up k inst_uparams].
  Proof.
    intros ->; apply inst_preserve_not.
  Qed.

  Definition All_notin k l :
    All (ind_sp_uparams_notin l_uparams_b k) l ->
    All (ind_sp_uparams_notin g_uparams_b (nb_cxt_sub + k))
            (map (fun t => t.[up k inst_uparams]) l).
  Proof.
    apply All_map. apply inst_preserve_not.
  Qed.

  Definition All_notin_eq k m l :
  m = nb_cxt_sub + k ->
  All (ind_sp_uparams_notin l_uparams_b k) l ->
  All (ind_sp_uparams_notin g_uparams_b m) (map (fun t => t.[up k inst_uparams]) l).
  Proof.
    intros ->; apply All_notin.
  Qed.

  Definition Alli_notin l k :
  Alli (ind_sp_uparams_notin l_uparams_b) k l ->
  Alli (ind_sp_uparams_notin g_uparams_b) (nb_cxt_sub + k)
          (mapi_rec (fun i t => t.[up i inst_uparams]) l k).
  Proof.
    rewrite Nat.add_comm.
    intros X; induction X ; cbn ; constructor; eauto.
    apply inst_preserve_not_eq => //. apply Nat.add_comm.
  Qed.

  Definition Alli_notin_eq l k m :
  m = (nb_cxt_sub + k) ->
  Alli (ind_sp_uparams_notin l_uparams_b) k l ->
  Alli (ind_sp_uparams_notin g_uparams_b) m
          (mapi_rec (fun i t => t.[up i inst_uparams]) l k).
  Proof.
    intros ->. apply Alli_notin.
  Qed.


  (* Lemma for subst *)
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

  Definition ind_sp_uparams_notin_subst up k i s :
    forall (t : term),
    All (ind_sp_uparams_notin up k) s ->
    ind_sp_uparams_notin up (k + i + #|s|) t ->
    ind_sp_uparams_notin up (k + i) (subst s i t).
  Proof.
    intros; apply on_free_vars_subst => //.
  Qed.

  Definition ind_sp_uparams_notin_subst_eq up k i s m n :
    forall (t : term),
    m = k + i + #|s| ->
    n = k + i ->
    All (ind_sp_uparams_notin up k) s ->
    ind_sp_uparams_notin up m t ->
    ind_sp_uparams_notin up n (subst s i t).
  Proof.
    intros t -> ->; apply on_free_vars_subst => //.
  Qed.

  Definition ind_sp_uparams_notin_subst_rev up k i s :
  forall (t : term),
  All (ind_sp_uparams_notin up k) s ->
  ind_sp_uparams_notin up (k + i + #|s|) t ->
  ind_sp_uparams_notin up (k + i) (subst (rev s) i t).
  Proof.
    intros. apply ind_sp_uparams_notin_subst => //.
    - apply All_rev => //.
    - now rewrite length_rev.
  Qed.

  Definition ind_sp_uparams_notin_subst_rev_eq up k i s m n :
    forall (t : term),
    m = k + i + #|s| ->
    n = k + i ->
    All (ind_sp_uparams_notin up k) s ->
    ind_sp_uparams_notin up m t ->
    ind_sp_uparams_notin up n (subst (rev s) i t).
  Proof.
    intros t -> ->; apply ind_sp_uparams_notin_subst_rev.
  Qed.







  (* The instanciation of the uniform parameters is defined in the context:

        g_uparams ,,, g_nuparams ,,, g_args ,,, g_largs |- inst_uparams

    Yet, the indices are defined in the context:

        l_uparams ,,, l_nuparams |- l_indices

    As the uniform and non-uniform parameters must be the same for all mutual
    inductive blocks g_uparams ,,, g_nuparams, we must move l_nuparams to indices.
    Moreover, we must add g_args ,,, g_largs to the indices for the subtitution
    of l_uparams in l_nuparams ,,, l_indices to be well-typed. This gives us:

        g_args ,,, g_largs ,,,  σ(l_nuparams ,,, indices)

    WARNING => this creates inductive-inductive types!
            => it SHOULD be possible to be finer only add the context really
               needed and stay mutual

      Sol1?: Make it so you only need the strict pos arg
        V1:
        => str pos can't be used in the rest of the context (needed anyway)
        => a polymorphic argument ?
        V2
        => add by hand it in the pos condition, should work but v1 would be better

    This also forces us to add g_args ,,, g_largs ,,,  σ(l_nuparams) as
    arguments of the constructors so that they can be refered in indices.

    Note 1 : Fundamentally g_args ,,, g_largs ,,,  σ(l_nuparams) are uparams
    they are indices only because this must be common to all blocks.
    That would be nice tough, as we wouldn't have to add them everywhere.

    Note 2 : We can not subtitute the intanciation of non-uniform pamareters nor
    indices as otherwise a constructor of the form  `c : nlist (A * A) -> nlist A`
    would become `c : nlist (nat * nat) -> nlist nat` and there would no longer
    be any way to build a term of type `nlist (nat * nat)`.

  *)

  (* TO BE FIXED LATED => how not to be ind-ind ?
     Just filter out g_args that are not free ? *)
  Definition new_indices indices : context :=
    g_args ,,, g_largs ,,, inst_context inst_uparams (l_nuparams ,,, indices).


  (* New Arguments + Positivity *)
  Definition cstr_new_args : list argument :=
       g_args_a
    ++ map arg_is_free g_largs_t
    ++ map arg_is_free (mapi_rec (fun i t => t.[up i inst_uparams])
        (terms_of_cxt l_nuparams) 0).

  Notation nb_new_args := #|cstr_new_args|.

  Definition nb_new_args_unfold : nb_new_args = nb_g_args + nb_g_largs + nb_l_nuparams.
  Proof.
    solve_length.
  Qed.

  Definition pos_cstr_new_args :
    Alli (positive_argument nb_m_block g_uparams_b true) nb_g_nuparams cstr_new_args.
  Proof.
    eapply Alli_impl; only 2: (intros; now apply pos_arg_inc).
    repeat apply Alli_app_inv; cbn.
    - assumption.
    - eapply Alli_map ; only 1: apply pos_arg_is_free. assumption.
    - eapply Alli_map ; only 1: apply pos_arg_is_free.
      apply Alli_notin_eq => //. solve_length.
  Defined.


  (* Specialization of Arguments *)

  (* Substitute a strictly positive uniform parameter by its instantiation *)
  (* largs, args : already updated arg to sub [∀ largs, A_k args]
     llargs, arg : already updated instantiation [λ llargs, arg] wth largs in the context
  *)
  Definition sub_uparam (largs : list term) (args : list term) (llargs : list term) (arg : argument) : argument :=
    match arg with
    | arg_is_free t => arg_is_free (it_tProd largs (mkApps (it_tLambda llargs t) args))
    | arg_is_sp_uparam ll k x =>
        let ll' := mapi (fun i => subst (rev args) i) ll in
        let x' := map (subst (rev args) #|ll|) x in
        arg_is_sp_uparam (largs ++ ll') k x'
    | arg_is_ind ll pos_indb i_upi =>
        let ll' := mapi (fun i => subst (rev args) i) ll in
        let i_upi' := map (subst (rev args) #|ll|) i_upi in
        arg_is_ind (largs ++ ll') pos_indb i_upi'
    | arg_is_nested ll ind u inst_up inst_else =>
        let ll' := mapi (fun i => subst (rev args) i) ll in
        let inst_up'  := map (fun ' (llargs, arg) =>
            let llargs' := mapi (fun i => subst (rev args) (#|ll| + i)) llargs in
            let arg' := subst_argument (rev args) (#|ll| + #|llargs|) arg in
            (llargs', arg')
            ) inst_up
          in
        let inst_else' := map (subst (rev args) #|ll|) inst_else in
        arg_is_nested (largs ++ ll') ind u inst_up' inst_else'
    end.

  Definition pos_sub_uparams pos_sub_cxt largs args (lax : bool) (llargs : list term) (arg : argument)
    (* contet substitution *)
    (pos_largs : Alli (ind_sp_uparams_notin g_uparams_b) (nb_cxt_sub + pos_sub_cxt) largs)
    (pos_args  : All  (ind_sp_uparams_notin g_uparams_b  (nb_cxt_sub + pos_sub_cxt + #|largs|)) args)
    (* arg to substitute by *)
    (* WARNING: Check pos *)
    (fapp_arg : #|llargs| = #|args|)
    (pos_llargs : Alli (ind_sp_uparams_notin g_uparams_b) (nb_cxt_sub + pos_sub_cxt + #|largs|) llargs)
    (pos_arg : positive_argument nb_m_block g_uparams_b lax (nb_cxt_sub + pos_sub_cxt + #|largs| + #|llargs|) arg)
    :
    positive_argument nb_m_block g_uparams_b lax
      (nb_cxt_sub + pos_sub_cxt) (sub_uparam largs args llargs arg).
  Proof.
    remember (nb_cxt_sub + pos_sub_cxt + #|largs| + #|llargs|) as p eqn:Heqp.
    induction pos_arg using positive_argument_rect' in Heqp |- *; cbn.
    + apply pos_arg_is_free. apply ind_sp_uparams_notin_tProd => //.
      apply ind_sp_uparams_notin_mkApps => //.
      eapply ind_sp_uparams_notin_tLambda_eq; tea.
      1: solve_length.
    + eapply pos_arg_is_sp_uparams => //.
      - cbn_length => //.
      - apply Alli_app_inv => //. eapply Alli_mapi. 2: eassumption.
        intros j x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all : rewrite ?Heqp; lia.
      - cbn_length. eapply All_map. 2: eassumption. cbn.
        intros x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all : rewrite ?Heqp; lia.
    + apply pos_arg_is_ind => //; cbn_length.
      - apply Alli_app_inv => //. eapply Alli_mapi. 2: eassumption.
        intros j x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all : rewrite ?Heqp; lia.
      - cbn_length. eapply All_map. 2: eassumption. cbn.
        intros x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all : rewrite ?Heqp; lia.
    + apply pos_arg_is_nested with (mdecl := mdecl) => //; cbn_length.
      - apply Alli_app_inv => //. eapply Alli_mapi. 2: eassumption.
        intros j x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all : rewrite ?Heqp; lia.
      - induction Ppos_nested; constructor. 2: apply IHPpos_nested.
        destruct x as [l_ll l_arg], y as [cdecl pos_arg], r as [[fapp pos_l_ll] pos_l_arg]; cbn in *.
        cbn_length; repeat split => //.
        * eapply Alli_mapi. 2: eassumption.
          intros j x H. eapply ind_sp_uparams_notin_subst_rev_eq.
          3: apply pos_args. 3: apply H.
          all : rewrite ?Heqp; lia.
        * clear p al Ppos_nested notin_instance IHPpos_nested.
          rewrite Heqp in pos_l_arg.
          eapply pos_subst_argument_eq.
          4: apply pos_l_arg.
          3: { apply All_rev. tea. }
          all : solve_length.
      - cbn_length. eapply All_map. 2: eassumption. cbn.
        intros x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all : rewrite ?Heqp; lia.
  Qed.

  Definition err_arg : list term * argument
    := ([], arg_is_free (tVar "impossible case")).

  (* Specialize an argument
  1. If it is a strpos uparams => substite by its instantiation
  2. Otherwise propagate the instantiation

  pos sub_cxt : how deep after the sub_contxt => needed to lift the instantiation
  *)
  Fixpoint specialize_argument (pos_sub_cxt : nat) (arg : argument) : argument :=
    match arg with
    | arg_is_free t =>
        arg_is_free (t.[up pos_sub_cxt inst_uparams])
    | arg_is_sp_uparam largs k args =>
        (* update largs and args of [∀ largs, A_k args] to sub *)
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams]) largs pos_sub_cxt in
        let args'  := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams]) args in
        (* get and lift the instantiation *)
        let ' (llargs, arg_to_sub) := nth k inst_uparams_a err_arg in
        let llargs := map (lift0 (pos_sub_cxt + #|largs|)) llargs in
        let arg_to_sub := lift_argument (pos_sub_cxt + #|largs|) 0 arg_to_sub in
        sub_uparam largs' args' llargs arg_to_sub
    | arg_is_ind largs i inst_uparams_indices =>
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams]) largs pos_sub_cxt in
        (* we need to add var for new nup + new indices - old_nup *)
        let new_indices := tRels (pos_sub_cxt + #|largs|) (nb_g_nuparams + #|g_args_a| + #|g_largs_t|) in
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

  Definition pos_specialize_argument pos_arg arg :
    positive_argument nb_l_block l_uparams_b true (nb_l_nuparams + pos_arg) arg ->
    positive_argument nb_m_block g_uparams_b true (nb_cxt_sub + nb_l_nuparams + pos_arg)
      (specialize_argument (nb_l_nuparams + pos_arg) arg).
  Proof.
    intros H. induction H; cbn.
    + apply pos_arg_is_free. apply inst_preserve_not_eq; only 1 : lia. assumption.
    + rewrite <- Nat.add_assoc.
      destruct (nth k inst_uparams_a err_arg) as [llargs arg_to_sub] eqn:H.
      apply eq_prod in H as [Hfst Hsnd].
      apply pos_sub_uparams. all: cbn_length.
      - apply Alli_notin_eq => //. lia.
      - apply All_notin_eq => //. lia.
      - rewrite - e0 -Hfst. symmetry.
        apply (All2_nth (fun n x => n = #|x.1|)); only 1: solve_length.
        apply fapp_inst_uparams.
      - eapply (Alli_map_gen_eq (n := nb_cxt_sub) (k := nb_l_nuparams + pos_arg + #|largs|)).
        * lia.
        * intros n x H. rewrite Nat.add_comm. unfold ind_sp_uparams_notin.
          rewrite -shiftnP_add. rewrite -{1}(Nat.add_0_r (nb_l_nuparams + pos_arg + #|largs|)).
          apply on_free_vars_lift_impl. rewrite shiftnP_add; cbn. exact H.
        * rewrite -Hfst. apply All_nth => //. 1: rewrite size_inst_uparams; lia.
          apply positive_inst_llargs.
      - unshelve eapply pos_lift_argument_eq0.
        * exact (nb_cxt_sub + #|llargs|).
        * lia.
        (* the arguments we subtitute is positive ???*)
        * rewrite -Hfst -Hsnd. apply All_nth => //. 1: rewrite size_inst_uparams; lia.
          admit.
    + apply pos_arg_is_ind.
      - reflexivity.
      - lia.
      - apply Alli_notin_eq => //. lia.
      - apply All_app_inv; cbn_length.
        -- unfold tRels. apply All_rev_pointwise_map. cbn.
           intros. apply shiftnP_lt. lia.
        -- apply All_notin_eq => //. solve_length.
    + apply pos_arg_is_nested with (mdecl := mdecl) => //.
      - admit.
      - admit.
      - admit.
  Admitted.


  (* The instanciation of the uniform parameters is defined in the context:

        g_uparams ,,, g_nuparams ,,, g_args ,,, g_largs |- inst_uparams

     The constructor are definied in the context

        l_uparams ,,, l_nuparams ,,, cstr_args |- cstr_indices

      We then have as a new type:

         (g_args ,,, g_largs), σ(l_nuparams ,,, cstr_args)
          |- new_indices ++ σ #|l_nupar + cstr_args| cstr_indices

      Note, we must also add cstr_indices as g_args ,,, g_largs), σ(l_nuparams)
      are now indices!
  *)


  Definition specialize_ctor (ctor : constructor_body) : constructor_body :=
  {|
    cstr_args    := cstr_new_args
                    ++ mapi (fun i => specialize_argument (nb_l_nuparams + i)) ctor.(cstr_args)  ;
    cstr_indices :=    tRels #|ctor.(cstr_args)| (#|g_args_a| + #|g_largs_t| + #|l_nuparams|)
                    ++ map (inst (up (nb_l_nuparams + #|ctor.(cstr_args)|) inst_uparams))
                           ctor.(cstr_indices)
  |}.


  Definition pos_specialize_ctor ctor :
    positive_constructor nb_l_block l_uparams_b l_nuparams ctor ->
    positive_constructor nb_m_block g_uparams_b g_nuparams (specialize_ctor ctor).
  Proof.
    unfold positive_constructor, specialize_ctor. cbn.
    intros [pos_cstr_args pos_cstr_indices]. split.
    (* pos args *)
    + apply Alli_app_inv.
      - apply pos_cstr_new_args.
      - eapply Alli_mapi; only 2: exact pos_cstr_args.
        intros. apply_eq (pos_specialize_argument i x) => //.
        solve_length.
    (* pos indices *)
    + cbn_length. apply All_app_inv.
      - unfold tRels. apply All_rev_pointwise_map; cbn.
        intros. apply shiftnP_lt. lia.
      - apply All_notin_eq; only 1: lia. assumption.
  Qed.

  Definition specialize_one_inductive_body (idecl : one_inductive_body) : one_inductive_body :=
  {|
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
    intros [Ha Hb]; split; cbn.
    - now eapply All_map; only 1: apply pos_specialize_ctor.
    (* one extra case if you want to prove it is not inductiv inductive *)
    - admit.
  Admitted.

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


  (* Fold Arguments *)
  Definition Acc : Type := list argument * list one_inductive_body.

  Definition PosArg n (arg : argument) : Type :=
    positive_argument nb_g_block g_uparams_b true (nb_g_nuparams + n) arg.

  Definition PosAcc (acc : Acc) : Type :=
      let nargs := acc.1 in let acc_indb := acc.2 in
       Alli (positive_argument (nb_g_block + #|acc_indb|) g_uparams_b true) nb_g_nuparams nargs
    * (All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb).

  (* fold_function *)
  Definition nested_to_mutual_one_argument (acc : Acc) (arg : argument) :
      Acc :=
    let nargs := acc.1 in let acc_indb := acc.2 in
    match arg with
    | arg_is_nested largs (mkInd kname pos_indb) u inst_uparams inst_nuparams_indices =>
      if option_map mutual_to_view (lookup_minductive E kname) is Some mdecl
      then (let new_indb := map (specialize_one_inductive_body (nb_g_block + #|acc_indb|)
                                  g_uparams_b g_nuparams nargs largs mdecl.(ind_nuparams)
                                  inst_uparams) mdecl.(ind_bodies) in
            (* we need to add var for new nup + new indices i.e *)
            let new_indices := tRels 0 (nb_g_nuparams + #|nargs| + #|largs|) in

          let new_arg := arg_is_ind largs (pos_indb + nb_g_block + #|acc_indb|)
                          (new_indices ++ inst_nuparams_indices) in
          (nargs ++ [new_arg], acc_indb ++ new_indb))
      else (nargs ++ [arg], acc_indb)
    | _ => (nargs ++ [arg], acc_indb)
    end.

  Definition pos_nested_to_mutual_one_argument (acc : Acc) arg :
    (* spec *)
    forall (pos_acc : PosAcc acc) (pos_arg : PosArg #|acc.1| arg),
    (* res *)
    PosAcc (nested_to_mutual_one_argument acc arg).
  Proof.
    destruct acc as [nargs acc_indb].
    unfold PosAcc, PosArg.
    intros [pos_nargs pos_acc_indb] pos_arg.
    (* new *)
    destruct pos_arg; cbn in *.
    all : try solve [split => //; apply Alli_app_inv => //; repeat constructor => //; try lia].
    rewrite e0; cbn. cbn_length.
    pose proof (p := E_pos kname); rewrite e0 in p; cbn in p.
    destruct p as [pos_l_nuparams pos_l_indb]. split.
    + apply Alli_app_inv; only 1: (eapply Alli_impl; tea; intros; apply pos_arg_inc) => //.
      repeat constructor => //.
      1: { rewrite -mutual_to_view_ind. lia. }
      apply All_app_inv => //.
      unfold tRels. apply All_rev_pointwise_map. cbn.
      intros. apply shiftnP_lt. lia.
    + apply All_app_inv; only 1: (eapply All_impl; tea; intros; apply pos_idecl_inc) => //.
      eapply All_map; [| apply pos_l_indb ].
      intros idecl. apply pos_specialize_idecl => //.
      (* * assumption. move => //. eapply Alli_impl; [ easy | auto using pos_arg_inc ]. *)
      eapply All2_impl; only 1: rewrite -mutual_to_view_uparams; tea.
      intros [llargs arg] [cdecl pos] [[fapp pos_llargs] pos_arg].
      cbn in *. repeat split; tea. apply pos_arg_inc => //.
  Qed.

  Definition length1_nested_to_mutual_one_argument acc arg :
    #|(nested_to_mutual_one_argument acc arg).1| = 1 + #|acc.1|.
  Proof.
    destruct arg; cbn.
    4: destruct ind; destruct (lookup_minductive E _).
    all: cbn_length; cbn; try lia.
  Qed.

  Definition spec_fl {X Y} (f : ((list X) * Y) -> X -> ((list X) * Y)) (xs : list X) (y : (list X) * Y)
    PY PX
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

  (* fold *)
  Definition pos_left acc args
    (pos_arg : Alli PosArg #|acc.1| args)
    (pos_acc : PosAcc acc)
    :
  PosAcc (fold_left nested_to_mutual_one_argument args acc).
  Proof.
    remember (#|acc.1|) as n.
    revert acc Heqn pos_acc.
    induction pos_arg; cbn. 1: easy.
    intros acc Heqn posAcc.
    apply IHpos_arg.
    - destruct hd; cbn_length; cbn; try lia.
      destruct ind. destruct (lookup_minductive E _) as [mdecl|]; cbn.
      all: cbn_length; cbn; try lia.
    - apply pos_nested_to_mutual_one_argument => //.
      rewrite -Heqn => //.
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
    (pos_args : Alli (positive_argument nb_g_block g_uparams_b true) nb_g_nuparams args)
    (pos_acc_indb : All (positive_one_inductive_body (nb_g_block + #|acc_indb|) g_uparams_b g_nuparams) acc_indb) :
    (* new_spec *)
    PosAcc (nested_to_mutual_argument args acc_indb).
  Proof.
    apply pos_left; cbn.
    - eapply Alli_shiftn_inv. rewrite Nat.add_comm => //.
    - split; [constructor | assumption].
  Qed.


  Definition nested_to_mutual_one_ctor ctor acc_indb :
    constructor_body * list one_inductive_body :=
  let x := nested_to_mutual_argument ctor.(cstr_args) acc_indb in
  let new_ctor := {|
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
    eapply spec_fl; cbn.
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
    eapply spec_fl; cbn.
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