(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
(* From MetaRocq.Common Require Import BasicAst Primitive Universes Environment. *)
(* From Equations.Prop Require Import Classes EqDecInstances. *)
(* From Coq Require Import List. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv.
From MetaRocq.PCUIC Require Import PCUICAuxToMove.
Import PCUICEnvironment.

(* Todo list:

### Positivity :
[X] 1. Def view
[X] 2. Def positivity
[X] 3. Recursor Positivity
[X] 4. Prove properties stablity addition block + lift

### Ind to View :
[ ] 1. Fix positive of Ind to include nested
[ ] 2. Translation ind to view
[ ] 3. Prove positivity is preserved

### View to Ind :
[ ] 1. Translation view to ind
[ ] 2. prove positivity is preserved

*)

Axiom todo_ : forall {A}, A.
#[warn(note="TO IMPLEMENT")] Notation todo := todo_.

Axiom todot_ : forall {A}, string -> A.
#[warn(note="TO IMPLEMENT")] Notation todot x := (todot_ x).

Axiom (PCUICEnv_ind_uparams : PCUICEnvironment.mutual_inductive_body -> list (context_decl × bool)).


Module ViewInductive.
(* *** Simplified Def of Inductive Types *** *)

(* An argument is either:
  - a term t that does not contain the ind nor the sp_uparams
  - of the form (∀ x1 ... xn, A / Ind i / tInd ...
  - pos_indb is the position of the block
  - k is the position of the uparam in the telescope
*)
Unset Elimination Schemes.

Inductive argument : Type :=
| arg_is_free      (t : term)
| arg_is_sp_uparam (largs : list term) (k : nat) (args : list term)
| arg_is_ind       (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term)
| arg_is_nested    (largs : list term) (ind : inductive) (u : Instance.t)
                    (inst_uparams : list (list term * argument)) (inst_nuparams_indices : list term).

Fixpoint argument_rect (P : argument -> Type)
  (Harg_is_free : (forall t : term, P (arg_is_free t)))
  (Harg_is_sp_uparam : forall (largs : list term) (k : nat) (args : list term),
                        P (arg_is_sp_uparam largs k args))
  (Harg_is_ind : forall (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term),
                 P (arg_is_ind largs pos_indb inst_nuparams_indices))
  (Harg_is_nested : forall (largs : list term) (ind : inductive) (u : Instance.t)
                    (inst_uparams : list (list term * argument))
                    (pos_inst_uparams : All (fun x => P x.2) inst_uparams)
                    (inst_nuparams_indices : list term),
                    P (arg_is_nested largs ind u inst_uparams inst_nuparams_indices)):
  forall (a : argument), P a.
Proof.
  intros a; destruct a.
  - apply Harg_is_free.
  - apply Harg_is_sp_uparam.
  - apply Harg_is_ind.
  - apply Harg_is_nested. induction inst_uparams; constructor.
    apply argument_rect; eauto. apply IHinst_uparams.
Qed.

Set Elimination Schemes.

(* A constructor is of the form (∀ args, tRel (n - cstr_pos -1) up nup indices *)
Record constructor_body := mkViewCtor {
  (** Constructor name, without the module path. *)
    cstr_name : ident;
  (* which constructors it corresponds to *)
    (* cstr_pos : nat;  ==>> necessary ? *)
  (* list of arguments *)
  cstr_args : list argument;
  (** Indices of the return type of the constructor *)
  cstr_indices : list term;
  }.

(* cstr_args : context;  ===>> list of arg (more work done)  *)
(* cstr_type : term;     ===>> removed because inferred *)
(* cstr_arity : nat;     ===>> no link pos
    cstr_pos : nat        ===>> added cause easier to check for pos
*)

(** Data associated to a single inductive in a mutual inductive block. *)
Record one_inductive_body := mkViewInd {
  (** Name of the inductive, without the module path. *)
  ind_name : ident;
  (** Indices of the inductive, which can depend on the parameters :
      `ind_params |- ind_indices`. *)
  ind_indices : context;
  (** Sort of the inductive. *)
  ind_sort : Sort.t;
  (** Full type of the inductive. This should be equal to
      `forall ind_params ind_indices, tSort ind_sort` *)
    (* ind_type : term; ===>> removed because inferred *)
  (** Allowed eliminations for the inductive. *)
  ind_kelim : allowed_eliminations;
  (** Constructors of the inductive. Order is important. *)
  ind_ctors : list constructor_body;
  (** Names and types of primitive projections, if any. *)
    (* ind_projs : list projection_body; => removed no link pos *)
  (** Relevance of the inductive. *)
  ind_relevance : relevance
  }.



(** Data associated to a block of mutually inductive types. *)
Record mutual_inductive_body := mkViewMut {
  (** Whether the block is inductive, coinductive or non-recursive (Records). *)
  ind_finite : recursivity_kind;
  (** Context of uniform parameters + if they are strictly postive *)
  ind_uparams : list (context_decl * bool);
  (** Context of non-uniform parameters *)
  ind_nuparams : context;
  (** Components of the mutual inductive block. Order is important. *)
  ind_bodies : list one_inductive_body ;
  (** Whether the mutual inductive is universe monomorphic or universe polymorphic,
      and information about the local universes if polymorphic. *)
  ind_universes : universes_decl;
  (** Variance information. `None` when non-cumulative. *)
  ind_variance : option (list Universes.Variance.t)
  }.

  (* ind_npars : nat ===>> computed  *)
  (* ind_params : context; => split in ind_uparams and ind_nuparams *)











(* *** Strict Positivity *** *)

Section PositiveIndBlock.

  Axiom (E : global_env).


  Definition andP {A} (P Q : A -> bool) := fun a => P a && Q a.
  Notation "P &&p Q" := (andP P Q) (at level 50).


  (* Context of the mutual inductive block *)
  Context (nb_block : nat).

  Context (uparams_b : list (context_decl * bool)).
  Definition uparams : context := map fst uparams_b.
  Notation nb_uparams := #|uparams_b|.

  Context (nuparams : context).
  Notation nb_nuparams := #|nuparams|.

  Definition params : context := uparams ,,, nuparams.


  (* Check for inds and strictly positive uparams with only that in the cxt *)
  Definition ind_notinP : nat -> bool :=
    fun n => if #|uparams_b| <=? n then false else true.

  Definition ind_notin pos_arg : term -> bool :=
    on_free_vars (shiftnP pos_arg ind_notinP).

  Definition sp_uparams_notinP : nat -> bool :=
    fun n => ~~ ((nth n (rev uparams_b) (todot "imp", false)).2).

  (* Definition sp_uparams_notinP : nat -> bool :=
  fun n => if nth_error (rev uparams_b) n is Some (_, b)
          then negb b else true. *)

  Definition sp_uparams_notin pos_arg : term -> bool :=
    on_free_vars (shiftnP pos_arg sp_uparams_notinP).

  Definition ind_sp_uparams_notinP : nat -> bool :=
    ind_notinP &&p sp_uparams_notinP.

  Definition ind_sp_uparams_notin pos_arg : term -> bool :=
    on_free_vars (shiftnP pos_arg ind_sp_uparams_notinP).

  Definition tRel_is_sp_uparams : nat -> bool :=
  fun k => nth k (map snd (rev uparams_b)) false.

  Definition ind_sp_uparams_notin_below k i :
    i <? k -> ind_sp_uparams_notin k (tRel i).
  Proof.
    cbn. unfold shiftnP. now intros ->.
  Qed.

  Definition shiftnP_ltb k P i :
    i <? k -> shiftnP k P i.
  Proof.
    unfold shiftnP. now intros ->.
  Qed.

  Definition shiftnP_lt k P i :
    i < k -> shiftnP k P i.
  Proof.
    intros H. apply shiftnP_ltb. now apply Nat.ltb_lt.
  Qed.



  (* lemma for binders *)
  (* already existing ??? on_free_var directly *)
  Definition ind_sp_uparams_notin_tProd k l t :
    Alli (ind_sp_uparams_notin) k l ->
    ind_sp_uparams_notin (k + #|l|) t ->
    ind_sp_uparams_notin k (it_tProd l t).
  Proof.
    todo " totod".
  Qed.

  Definition ind_sp_uparams_notin_tLambda (k : nat) (l : list term) (t : term) :
    Alli (ind_sp_uparams_notin) k l ->
    ind_sp_uparams_notin (k + #|l|) t ->
    ind_sp_uparams_notin k (it_tLambda l t).
  Proof.
    todo " totod".
  Qed.

  Definition ind_sp_uparams_notin_tLambda_eq k l t m :
    m = k + #|l| ->
    Alli (ind_sp_uparams_notin) k l ->
    ind_sp_uparams_notin m t ->
    ind_sp_uparams_notin k (it_tLambda l t).
  Proof.
    todo " totod".
  Qed.

  Definition ind_sp_uparams_notin_mkApps k u vs :
    All (ind_sp_uparams_notin k) vs ->
    ind_sp_uparams_notin k u ->
    ind_sp_uparams_notin k (mkApps u vs).
  Proof.
    todo " totod".
  Qed.

  (* Positivity part *)

  (* An argument is positive if:
    - It is a term t and ind + sp_uparams ∉ x1 ... xn
    - It is of the form ∀ x1 ... xn, A / Ind i / tInd, x1 ... xn and,
      1. ind + sp_uparams ∉ x1 ... xn
      2. It ends with:
        - a lax postitive uniform parameter A y1 ... yn, and ind + sp_uparams ∉ y1 ... yn
        - one of the inductive block (Ind i) y1 ... yn, and ind + sp_uparams ∉ y1 ... yn
        - a nested occurence, the instantiation of the sp uparams is positive the others is not nested,
          ind + sp_uparams ∉ instantiations of nuparams and indices
  *)

  Definition cdecl_to_arity : context_decl -> nat :=
    todo.

  Definition uparams_nb_args : list nat :=
    map (fun x => cdecl_to_arity x.1) uparams_b.


  Reserved Notation " lax |> size_cxt |arg+> t " (at level 50, t at next level).

  (* Unset Elimination Schemes. *)

  Section PosArg.

  Context (Γargs : list argument).
  Notation nb_args := #|Γargs|.

  Notation size_cxt := (nb_nuparams + nb_args).

  (* size_cxt := nb_ binders already seen => nested case *)
  Inductive positive_argument (lax : bool) (nb_binders : nat) : argument -> Type :=
  | pos_arg_is_free t :
    ind_sp_uparams_notin (size_cxt + nb_binders) t ->
    lax |> nb_binders |arg+> arg_is_free t

  | pos_arg_is_sp_uparams largs k inst_args :
    lax = true ->
    (* it is a uparams *)
    k < #|uparams_b| ->
    (* which is positive *)
    nth k (map snd (rev uparams_b)) false ->
    (* and fully applied *)
    nth k (rev uparams_nb_args) 0 = #|inst_args| ->
    (* ind + sp_uparams ∉ largs *)
    Alli ind_sp_uparams_notin (size_cxt + nb_binders) largs ->
    (* ind + sp_uparams ∉ args *)
    All (ind_sp_uparams_notin (size_cxt + nb_binders + #|largs|)) inst_args ->
    (* -------------------------------------------------------------- *)
    lax |> nb_binders |arg+> arg_is_sp_uparam largs k inst_args

  | pos_arg_is_ind largs pos_indb inst_nuparams_indices :
    lax = true ->
    (* pos_indb corresponds to an inductive block *)
    pos_indb < nb_block ->
    (* ind + sp_uparams ∉ largs *)
    Alli ind_sp_uparams_notin (size_cxt + nb_binders) largs ->
    (* ind + sp_uparams ∉ inst_nuparams_indices *)
    All (ind_sp_uparams_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices ->
    (* -------------------------------------------------------------- *)
    lax |> nb_binders |arg+> arg_is_ind largs pos_indb inst_nuparams_indices

  | pos_arg_is_nested largs kname pos_ind u inst_uparams inst_nuparams_indices mdecl :
    lax = true ->
    (* ind + sp_uparams ∉ largs *)
    Alli ind_sp_uparams_notin (size_cxt + nb_binders) largs ->
    (* ind + sp_uparams ∉ inst_nuparams_indices *)
    All (ind_sp_uparams_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices ->
    (* declared mdecl + pos_ind *)
    lookup_minductive E kname = Some mdecl ->
    pos_ind < #|PCUICEnvironment.ind_bodies mdecl| ->
    (* inst_uparams are positive *)
    All2 (fun x y =>
      (* fully applied ensured by typing*)
      (#|x.1| = cdecl_to_arity y.1)
      (* llargs are free *)
      * Alli (ind_sp_uparams_notin) (size_cxt + nb_binders + #|largs|) x.1
      (* args are pos lax or strict depending if you can nest or not *)
      * positive_argument y.2 (nb_binders + #|largs| + #|x.1|) x.2
    ) inst_uparams (rev (PCUICEnv_ind_uparams mdecl))
    ->
    (* -------------------------------------------------------------- *)
    lax |> nb_binders |arg+> arg_is_nested largs (mkInd kname pos_ind) u
                              inst_uparams inst_nuparams_indices

  where "lax |> nb_binders |arg+> t " := (positive_argument lax nb_binders t) : type_scope.

  Inductive All2_param1 {A B R} (PR : forall a b, R a b -> Type) : forall {lA lB}, All2 R lA lB -> Type :=
  | All2_nil_param1 : All2_param1 PR ( @All2_nil A B R)
  | All2_cons_param1 : forall (x : A) (y : B) (l : list A) (l' : list B),
                forall (r : R x y), PR _ _ r ->
                forall (al : All2 R l l'), All2_param1 PR al ->
                All2_param1 PR (All2_cons r al).

  Definition positive_argument_rect'
    (P : forall {lax nb_binders arg}, positive_argument lax nb_binders arg -> Type)
    (P_arg_is_free :
        forall lax nb_binders (t : term) (i : ind_sp_uparams_notin (size_cxt + nb_binders) t),
        (* ------------------------ *)
        P (pos_arg_is_free lax nb_binders t i)
      )
    (P_arg_is_sp_uparams :
        forall lax nb_binders (largs : list term) (k : nat) (inst_args : list term)
        (e : lax = true) (pos_k : k < #|uparams_b|)
        (is_sp : nth k (map snd (rev uparams_b)) false)
        (fapp : nth k (rev uparams_nb_args) 0 = #|inst_args|)
        (notin_largs : Alli ind_sp_uparams_notin (size_cxt + nb_binders) largs)
        (notin_args : All (ind_sp_uparams_notin (size_cxt + nb_binders + #|largs|)) inst_args),
        (* ------------------------ *)
        P (pos_arg_is_sp_uparams lax nb_binders largs k inst_args e pos_k is_sp fapp notin_largs notin_args)
      )
    (P_arg_is_ind :
        forall lax nb_binders (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term)
        (e : lax = true) (pos_ind : pos_indb < nb_block)
        (notin_largs : Alli ind_sp_uparams_notin (size_cxt + nb_binders) largs)
        (notin_args : All (ind_sp_uparams_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices),
        (* ------------------------ *)
        P (pos_arg_is_ind lax nb_binders largs pos_indb inst_nuparams_indices
              e pos_ind notin_largs notin_args)
      )
    (P_arg_is_nested:
        forall lax nb_binders (largs : list term) (kname : kername) (pos_ind : nat) (u : Instance.t)
        (inst_uparams : list (list term × argument)) (inst_nuparams_indices : list term)
        (mdecl : PCUICEnvironment.mutual_inductive_body)
        (e : lax = true)
        (notin_largs : Alli ind_sp_uparams_notin (size_cxt + nb_binders) largs)
        (notin_instance : All (ind_sp_uparams_notin (size_cxt + nb_binders + #|largs|)) inst_nuparams_indices)
        (ind_env_defined : lookup_minductive E kname = Some mdecl)
        (ind_pos_defined : pos_ind < #|PCUICEnvironment.ind_bodies mdecl|)
        (pos_nested :
            All2 (fun (x : list term × argument) (y : context_decl × bool) =>
              (#|x.1| = cdecl_to_arity y.1
              × Alli (fun (pos_arg : nat) (x0 : term) => ind_sp_uparams_notin pos_arg x0) (size_cxt + nb_binders + #|largs|) x.1)
              * (positive_argument y.2 (nb_binders + #|largs| + #|x.1|) x.2))
            inst_uparams (rev (PCUICEnv_ind_uparams mdecl)))
        (Ppos_nested : All2_param1 (fun x y r => P r.2) pos_nested),
        (* ------------------------ *)
        P (pos_arg_is_nested lax nb_binders largs kname pos_ind u inst_uparams inst_nuparams_indices mdecl
              e notin_largs notin_instance ind_env_defined ind_pos_defined pos_nested)
      )
    : forall lax nb_binders arg (p : positive_argument lax nb_binders arg), P p.
  Proof.
    fix rec 4.
    intros ? ? ? p. destruct p as [ | | | ? ? ? ? ? ? ? ? ? ? ? ? pos_nested].
    - apply P_arg_is_free.
    - apply P_arg_is_sp_uparams.
    - apply P_arg_is_ind.
    - apply P_arg_is_nested.
      induction pos_nested; constructor; cbn.
      destruct x; destruct y; cbn.
      apply rec. apply IHpos_nested.
  Defined.

  Definition positive_argument_strict {size_cxt arg} :
    positive_argument false size_cxt arg ->
    ∑ t, arg = arg_is_free t.
  Proof.
    intro k; inversion k.
    1: eauto.
    all : lia.
  Qed.

  Definition pos_argument_from_false {size_cxt lax arg} :
    positive_argument false size_cxt arg ->
    positive_argument lax size_cxt arg.
  Proof.
    intros k; inversion k; only 2-4: lia.
    apply pos_arg_is_free => //.
  Qed.

  End PosArg.

  (* A constructor is postive when:
     1. All of its arguments are positive
     2. The return indices do not contain the inductives nor the sp_uparams
  *)
  Definition positive_constructor (ctor : constructor_body) : Type :=
      All_telescope (fun Γargs arg => positive_argument Γargs true 0 arg) ctor.(cstr_args)
   * All (ind_sp_uparams_notin (#|nuparams| + #|ctor.(cstr_args)|)) ctor.(cstr_indices).


(* A inductive body is positive when:
  - All its constructors are postive
  - The indices do not mention the sp uparams. This restriction is needed to
    ensure that the associated mutual type is not inductive-inductive
  *)
  Definition positive_one_inductive_body (indb : one_inductive_body) : Type :=
      All positive_constructor indb.(ind_ctors)
    (* To add to prevent inductive inductive *)
    * Alli (sp_uparams_notin) #|nuparams| (map decl_type (rev indb.(ind_indices))).

End PositiveIndBlock.

Definition positive_mutual_inductive_body (mdecl : mutual_inductive_body) : Type :=
    Alli (ind_sp_uparams_notin mdecl.(ind_uparams)) 0 (terms_of_cxt mdecl.(ind_nuparams))
  * All (positive_one_inductive_body #|mdecl.(ind_bodies)| mdecl.(ind_uparams)
        mdecl.(ind_nuparams)) mdecl.(ind_bodies).



(* Increasing the number of inductive block preserve positivity *)
Definition pos_arg_inc {nb_block up nup Γargs lax nb_binders arg} k :
  positive_argument nb_block up nup Γargs lax nb_binders arg ->
  positive_argument (nb_block + k) up nup Γargs lax nb_binders arg.
Proof.
  intros pos_arg. induction pos_arg using positive_argument_rect'.
  - constructor => //.
  - constructor => //.
  - constructor => //. lia.
  - econstructor; tea.
    induction Ppos_nested; cbn in *; constructor.
    + destruct r as [[]]; repeat constructor => //.
    + apply IHPpos_nested.
Qed.

Fixpoint pos_ctor_inc {nb_block up nup ctor} k :
  positive_constructor nb_block up nup ctor ->
  positive_constructor (nb_block + k) up nup ctor.
Proof.
  intros [pos_args pos_indices]; split => //.
  eapply All_telescope_impl; tea.
  intros; apply pos_arg_inc => //.
Qed.

Fixpoint pos_ctor_inc_le {nb_block up nup ctor} k :
  nb_block <= k ->
  positive_constructor nb_block up nup ctor ->
  positive_constructor k up nup ctor.
Proof.
  intros p%(Arith_base.le_plus_minus_stt _ _); rewrite p.
  apply pos_ctor_inc.
Qed.

Fixpoint pos_idecl_inc {nb_block up nup idecl} k :
  positive_one_inductive_body nb_block up nup idecl ->
  positive_one_inductive_body (nb_block + k) up nup idecl.
Proof.
  intros [pos_ctor pos_indices]; split => //.
  eapply All_impl; tea.
  intros; apply pos_ctor_inc => //.
Qed.

Fixpoint pos_idecl_inc_le {nb_block up pos_arg idecl} k :
  nb_block <= k ->
  positive_one_inductive_body nb_block up pos_arg idecl ->
  positive_one_inductive_body k up pos_arg idecl.
Proof.
  intros p%(Arith_base.le_plus_minus_stt _ _); rewrite p.
  apply pos_idecl_inc.
Qed.

Definition All_eq_notin up n m l :
  n = m ->
  All (fun x => ind_sp_uparams_notin up n x) l ->
  All (fun x => ind_sp_uparams_notin up m x) l.
Proof.
  intros -> X; exact X.
Qed.

Definition Alli_eq_notin up n m l :
  n = m ->
  Alli (fun n x => ind_sp_uparams_notin up n x) n l ->
  Alli (fun n x => ind_sp_uparams_notin up n x) m l.
Proof.
  intros -> X; exact X.
Qed.

Definition eq_notin up n m x :
  n = m ->
  ind_sp_uparams_notin up n x ->
  ind_sp_uparams_notin up m x.
Proof.
  intros -> X; exact X.
Qed.

Definition pos_arg_notin_unfold {nb_block up nup Γargs lax tm nb_binders} arg :
  positive_argument nb_block up nup Γargs lax (#|tm| + nb_binders) arg ->
  positive_argument nb_block up nup (Γargs ++ map arg_is_free tm) lax nb_binders arg.
Proof.
  remember (#|tm| + nb_binders) as p eqn:Heqp.
  intros pos_arg. revert nb_binders Heqp. induction pos_arg using positive_argument_rect'.
  all: (ltac2:(nconstructor 4)); cbn_length => //; tea;
       try solve [apply_eq notin_largs; solve_length | eapply All_eq_notin; tea; solve_length].
  + eapply eq_notin; tea; solve_length.
  + induction Ppos_nested as [|[llargs arg] [cdecl pos] inst_uparams uparams
          [[fapp pos_llargs] pos_inst] pos_arg RL IHRL ?]; constructor; eauto.
    cbn in *; cbn_length; repeat split => //.
    - apply_eq pos_llargs. solve_length.
    - apply_eq pos_arg. lia.
Qed.

Definition pos_arg_notin_fold {nb_block up nup Γargs lax tm nb_binders} arg :
  positive_argument nb_block up nup (Γargs ++ map arg_is_free tm) lax nb_binders arg ->
  positive_argument nb_block up nup Γargs lax (#|tm| + nb_binders) arg.
Proof.
  intros pos_arg; induction pos_arg using positive_argument_rect'.
  all: (ltac2:(nconstructor 4)); cbn_length => //; tea;
       try solve [apply_eq notin_largs; solve_length | eapply All_eq_notin; tea; solve_length].
  + eapply eq_notin; tea; solve_length.
  + induction Ppos_nested as [|[llargs arg] [cdecl pos] inst_uparams uparams
          [[fapp pos_llargs] pos_inst] pos_arg RL IHRL ?]; constructor; eauto.
    cbn in *; cbn_length; repeat split => //.
    - apply_eq pos_llargs. solve_length.
    - apply_eq pos_arg. lia.
Qed.


(* Lifting an argument preserves positivity *)
Fixpoint lift_argument n above (t : argument) {struct t} : argument :=
  match t with
  | arg_is_free t => arg_is_free (lift n above t)
  | arg_is_sp_uparam largs k inst_args =>
      let largs' := mapi (fun i => lift n (above + i)) largs in
      let inst_args' := map (lift n (above + #|largs|)) inst_args in
      arg_is_sp_uparam largs' k inst_args'
  | arg_is_ind largs pos_indb inst_nuparams_indices =>
      let largs' := mapi (fun i => lift n (above + i)) largs in
      let inst_nuparams_indices' := map (lift n (above + #|largs|)) inst_nuparams_indices in
      arg_is_ind largs' pos_indb inst_nuparams_indices'
  | arg_is_nested largs ind u inst_uparams inst_nuparams_indices =>
      let largs' := mapi (fun i => lift n (above + i)) largs in
      let inst_uparams' := map
        (fun '(llargs, arg) => ( mapi (fun i => lift n (above + #|largs| + i)) llargs,
                                 lift_argument n (above + #|largs| + #|llargs|) arg))
        inst_uparams in
      let inst_nuparams_indices' := map (lift n (above + #|largs|)) inst_nuparams_indices in
      arg_is_nested largs' ind u inst_uparams' inst_nuparams_indices'
  end.

Definition on_free_vars_lift (p : nat -> bool) (c n k : nat)
  (t : term) (ft : on_free_vars (shiftnP (c + k) p) t) :
  on_free_vars (shiftnP (c + n + k) p) (lift n k t).
Proof.
  rewrite -Nat.add_assoc Nat.add_comm -shiftnP_add.
  apply on_free_vars_lift_impl.
  rewrite shiftnP_add Nat.add_comm => //.
Qed.

Definition on_free_vars_lift' (p : nat -> bool) (c n k : nat)
  (t : term) (ft : on_free_vars (shiftnP (c + k) p) t) :
  on_free_vars (shiftnP (c + (n + k)) p) (lift n k t).
Proof.
  rewrite Nat.add_assoc. apply on_free_vars_lift => //.
Qed.

Definition on_free_vars_lift_eq (p : nat -> bool) (a b c n k : nat)
  (t : term) (eaq : a = c + k) (eqb : b = c + n + k) :
  on_free_vars (shiftnP a p) t ->
  on_free_vars (shiftnP b p) (lift n k t).
Proof.
  rewrite eaq eqb. apply on_free_vars_lift.
Qed.

Tactic Notation "solve_Alli" :=
  eapply Alli_mapi; only 2 :tea; intros i t;
  eapply on_free_vars_lift_eq; cbn_length; (reflexivity || lia).

Tactic Notation "solve_All" :=
  eapply All_map ; only 2: tea ; cbn; cbn_length; intros t;
  eapply on_free_vars_lift_eq; cbn_length; (reflexivity || lia).

Definition pos_lift_argument {nb_block up nup Γargs1 Γargs2 lax nb_binders} arg p n k :
  positive_argument nb_block up nup Γargs1 lax p arg ->
  p = (nb_binders + k) ->
  positive_argument nb_block up nup (Γargs1 ++ Γargs2) lax (nb_binders + n + k) (lift_argument (#|Γargs2| + n) k arg).
Proof.
  intro pos_arg. revert k.
  induction pos_arg using positive_argument_rect'; intros k0 ->.
  all: (ltac2:(nconstructor 4)); cbn_length => //; tea; try solve [solve_Alli | solve_All].
  + eapply on_free_vars_lift_eq; tea; cbn_length; reflexivity || lia.
  + fold lift_argument.
    induction Ppos_nested as [|[llargs arg] [cdecl pos] inst_uparams uparams
            [[fapp pos_llargs] pos_inst] pos_arg RL IHRL ?]; constructor; eauto.
    cbn in *; cbn_length; repeat split => //.
    - solve_Alli.
    - apply_eq pos_arg. all:lia.
Qed.

Definition pos_lift_argument_eq {nb_block up nup Γargs1 Γargs2 lax nb_binders} arg p Γ q r n k :
  p = nb_binders + k ->
  Γ = Γargs1 ++ Γargs2 ->
  q = nb_binders + n + k ->
  r = #|Γargs2| + n ->
  positive_argument nb_block up nup Γargs1 lax p arg ->
  positive_argument nb_block up nup Γ lax q (lift_argument r k arg).
Proof.
  intros ? -> -> -> X. eapply pos_lift_argument; tea.
Qed.


Fixpoint subst_argument l above (arg : argument) {struct arg} : argument :=
  match arg with
  | arg_is_free t => arg_is_free (subst l above t)
  | arg_is_sp_uparam largs k args =>
      let largs' := mapi (fun i => subst l (above + i)) largs in
      let args' := map (subst l (above + #|largs|)) args in
      arg_is_sp_uparam largs' k args'
  | arg_is_ind largs pos_indb inst_nuparams_indices =>
      let largs' := mapi (fun i => subst l (above + i)) largs in
      let inst_nuparams_indices' := map (subst l (above + #|largs|)) inst_nuparams_indices in
      arg_is_ind largs' pos_indb inst_nuparams_indices'
  | arg_is_nested largs ind u inst_uparams inst_nuparams_indices =>
      let largs' := mapi (fun i => subst l (above + i)) largs in
      let inst_uparams' := map
        (fun '(llargs, arg) => ( mapi (fun i => subst l (above + #|largs| + i)) llargs,
                                 subst_argument l (above + #|largs| + #|llargs|) arg))
        inst_uparams in
      let inst_nuparams_indices' := map (subst l (above + #|largs|)) inst_nuparams_indices in
      arg_is_nested largs' ind u inst_uparams' inst_nuparams_indices'
  end.

Definition pos_subst_argument {nb_block up nup Γargs lax nb_binders} sub above arg  :
  All (ind_sp_uparams_notin up ((#|nup| + #|Γargs|) + nb_binders)) sub ->
  positive_argument nb_block up nup Γargs lax (nb_binders + #|sub| + above) arg ->
  positive_argument nb_block up nup Γargs lax (nb_binders + above) (subst_argument sub above arg).
Proof.
Admitted.

Definition pos_subst_argument_eq {nb_block up nup Γargs lax nb_binders} sub above arg p q j :
  p = nb_binders + #|sub| + above ->
  q = nb_binders + above ->
  j = #|nup| + #|Γargs| + nb_binders ->
  All (ind_sp_uparams_notin up j) sub ->
  positive_argument nb_block up nup Γargs lax p arg ->
  positive_argument nb_block up nup Γargs lax q (subst_argument sub above arg).
Proof.
  intros -> -> ->; apply pos_subst_argument.
Qed.








(* *** View to Env *** *)

Section ViewToEnv.
  Context (nb_block : nat).
  Context (uparams_b : list (context_decl * bool)).
  Notation nb_uparams := #|uparams_b|.

  (* size_cxt := param + nuparam + args already seen *)
  Fixpoint argument_to_term (size_cxt : nat) (arg : argument) : term :=
    match arg with
    | arg_is_free t => t
    | arg_is_sp_uparam largs pos_uparams args =>
        let rel_uparams := (size_cxt - pos_uparams - 1) + #|largs| in
        it_tProd largs (mkApps (tRel rel_uparams) args)
    | arg_is_ind largs pos_indb inst_nuparams_indices =>
        let rel_indb := size_cxt + (nb_block - pos_indb - 1) + #|largs|in
        let up := tRels ((size_cxt - nb_uparams -1) + #|largs|) nb_uparams in
        it_tProd largs (mkApps (tRel rel_indb) (up ++ inst_nuparams_indices))
    | arg_is_nested largs ind u inst_uparams inst_nuparams_indices =>
        let term_uparams := map (fun ' (llargs, arg) =>
            it_tLambda llargs (argument_to_term (size_cxt + #|largs| + #|llargs|) arg)
          ) inst_uparams in
        it_tProd largs (mkApps (tInd ind u) (term_uparams ++ inst_nuparams_indices))
    end.

  Definition arguments_to_context (size_cxt : nat) (args : list argument) : context :=
    rev (mapi (fun i t => vassAR (argument_to_term (size_cxt + i) t)) args).

  Context (nuparams : context).
  Notation nb_nuparams := #|nuparams|.

  (* size_cxt := param + nuparam + args *)
  Definition return_type (size_cxt : nat) (indices : list term) : term :=
    let rel_indb := size_cxt + (nb_block - size_cxt - 1) in
    let up_nup := tRels (size_cxt - nb_uparams - nb_nuparams -1) (nb_uparams + nb_nuparams) in
    mkApps (tRel rel_indb) (up_nup ++ indices).

  Definition view_to_env_constructor : ViewInductive.constructor_body -> PCUICEnvironment.constructor_body :=
    fun ' (ViewInductive.mkViewCtor name args indices) => {|
      PCUICEnvironment.cstr_name := name;
      PCUICEnvironment.cstr_args := arguments_to_context (nb_uparams + nb_nuparams) args;
      PCUICEnvironment.cstr_indices := indices;
      PCUICEnvironment.cstr_type :=
        it_mkProd_or_LetIn (map fst uparams_b ++ nuparams ++
          arguments_to_context (nb_uparams + nb_nuparams) args)
          (return_type (nb_uparams + nb_nuparams + #|args|) indices)
        ;
      PCUICEnvironment.cstr_arity := #|args|
    |}.

  Print PCUICEnvironment.mutual_inductive_body.

  Definition view_to_env_indb : ViewInductive.one_inductive_body -> PCUICEnvironment.one_inductive_body :=
    fun ' (ViewInductive.mkViewInd name indices s kelim ctors relev) => {|
      PCUICEnvironment.ind_name := name;
      PCUICEnvironment.ind_indices := indices;
      PCUICEnvironment.ind_sort := s;
      PCUICEnvironment.ind_type := it_mkProd_or_LetIn (map fst uparams_b ++ nuparams ++ indices) (tSort s);
      PCUICEnvironment.ind_kelim := kelim;
      PCUICEnvironment.ind_ctors := map view_to_env_constructor ctors ;
      PCUICEnvironment.ind_projs := todo;
      PCUICEnvironment.ind_relevance := relev;
    |}.

  End ViewToEnv.

  Definition view_to_env_mut : ViewInductive.mutual_inductive_body -> PCUICEnvironment.mutual_inductive_body :=
    fun ' (ViewInductive.mkViewMut fin up nup indb u var) => {|
      PCUICEnvironment.ind_finite := fin;
      PCUICEnvironment.ind_npars := todo;
      PCUICEnvironment.ind_params := todo;
      PCUICEnvironment.ind_bodies := map (view_to_env_indb #|indb| up nup) indb ;
      PCUICEnvironment.ind_universes := u;
      PCUICEnvironment.ind_variance := var
    |}.

End ViewInductive.

Definition mutual_to_view : PCUICEnvironment.mutual_inductive_body ->
                            ViewInductive.mutual_inductive_body :=
  todot "to implem".

Definition mutual_to_view_ind mdecl :
  #|PCUICEnvironment.ind_bodies mdecl| = #|ViewInductive.ind_bodies (mutual_to_view mdecl)|.
Admitted.

Definition mutual_to_view_uparams mdecl :
  PCUICEnv_ind_uparams mdecl = ViewInductive.ind_uparams (mutual_to_view mdecl).
Admitted.

(*
(* PCUIC.Env -> View *)
Fixpoint inductive_to_view (mdecl : PCUICEnvironment.mutual_inductive_body)
  i Γ t (pos_t : positive_cstr mdecl i Γ t) : View.argument :=
  match pos_t with
  (* | pos_concl l (headrel := (#|mdecl.(ind_bodies)| - S i + #|Γ|)%nat) :
  All (closedn #|Γ|) l ->
  mdecl @ i ;;; Γ |+> mkApps (tRel headrel) l *)
  | pos_concl l _ => todo ""

  (* | pos_let na b ty ty' :
    mdecl @ i ;;; Γ |+> ty' {0 := b} ->
    mdecl @ i ;;; Γ |+> tLetIn na b ty ty' *)
  | pos_let na b ty ty' Hty0 => todo ""

  (* | pos_ass na ty ty' :
    mdecl ;;; Γ |arg+> ty ->
    mdecl @ i ;;; vass na ty :: Γ |+> ty' ->
    mdecl @ i ;;; Γ |+> tProd na ty ty' *)
  | pos_ass na arg B pos_arg pos_B => todo ""
  end.
*)
