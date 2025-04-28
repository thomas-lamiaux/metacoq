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

(* From Ltac2 Require Import Ltac2.

Ltac2  *)

(* Todo list:

[ ] 1. Translation view to nested
[ ] 2. Fix the positivity of ind
[ ] 3. Translation ind to view
[ ] 4. Proof pos ind -> pos view
[ ] 5. Proof pos view -> pos ind

*)

Module View.

Axiom todo_ : forall {A}, A.
#[warn(note="TO IMPLEMENT")] Notation todo := todo_.

Axiom todot_ : forall {A}, string -> A.
#[warn(note="TO IMPLEMENT")] Notation todot x := (todot_ x).


(* *** Simplified Def of Inductive Types *** *)

(* An argument is either:
  - a term t that does not contain the ind nor the sp_uparams
  - of the form (∀ x1 ... xn, A / Ind i / tInd ...
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
Record constructor_body := {
  (** Constructor name, without the module path. *)
    (* cstr_name : ident; ==>> does not matter for positivity *)
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
Record one_inductive_body := {
  (** Name of the inductive, without the module path. *)
    (* ind_name : ident; ===>> no link with positivity *)
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
Record mutual_inductive_body := {
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



(* functions on arguments *)
Definition argument_to_term (nb_block : nat) (pos_arg : nat) (arg : argument) : term :=
  match arg with
  | arg_is_free t => t
  | arg_is_sp_uparam largs k args =>
      it_tProd largs (mkApps (tRel k) args)
  | arg_is_ind largs pos_indb inst_nuparams_indices =>
      let rel_indb := pos_arg + #|largs| + (nb_block - pos_indb - 1) in
      it_tProd largs (mkApps (tRel rel_indb) inst_nuparams_indices)
  | arg_is_nested largs ind u inst_uparams inst_nuparams_indices =>
      let args := todo "to update" in
      (* let args := map (argument_to_term nb_block (pos_arg + #|largs|)) inst_uparams
                  ++ inst_nuparams_indices in *)
      it_tProd largs (mkApps (tInd ind u) args)
  end.

Definition arguments_to_context (nb_block : nat) (pos_arg : nat) (args : list argument) : context :=
rev (mapi (fun i t => vassAR (argument_to_term nb_block (i + pos_arg) t)) args).

Definition ctor_to_type (pos_ctor : nat) (ctor : constant_body) : term :=
  todo.

Definition idecl_to_type : context -> one_inductive_body -> term :=
  fun params idecl =>
  it_mkLambda_or_LetIn (params ,,, idecl.(ind_indices)) (tSort idecl.(ind_sort)).


Axiom (PCUICEnv_ind_uparams : PCUICEnvironment.mutual_inductive_body -> list (context_decl × bool)).
Axiom (E : global_env).







(* *** Strict Positivity *** *)

Section PositiveIndBlock.

  Definition andP {A} (P Q : A -> bool) := fun a => P a && Q a.
  Notation "P &&p Q" := (andP P Q) (at level 50).


  (* Context of the mutual inductive block *)
    Context (nb_block : nat).

  Context (uparams_b : list (context_decl * bool)).
  Definition uparams : context := map fst uparams_b.

  Context (nuparams : context).

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

  Inductive positive_argument (lax : bool) (size_cxt : nat) : argument -> Type :=
  | pos_arg_is_free t :
    ind_sp_uparams_notin size_cxt t ->
    lax |> size_cxt |arg+> arg_is_free t

  | pos_arg_is_sp_uparams largs k args :
    lax = true ->
    (* it is a uparams *)
    k < #|uparams_b| ->
    (* which is positive *)
    nth k (map snd (rev uparams_b)) false ->
    (* and fully applied *)
    nth k (rev uparams_nb_args) 0 = #|args| ->
    (* ind + sp_uparams ∉ largs *)
    Alli ind_sp_uparams_notin size_cxt largs ->
    (* ind + sp_uparams ∉ args *)
    All (ind_sp_uparams_notin (size_cxt + #|largs|)) args ->
    lax |> size_cxt |arg+> arg_is_sp_uparam largs k args

  | pos_arg_is_ind largs pos_indb inst_nuparams_indices :
    lax = true ->
    (* pos_indb corresponds to an inductive block *)
    pos_indb < nb_block ->
    (* ind + sp_uparams ∉ largs *)
    Alli ind_sp_uparams_notin size_cxt largs ->
    (* ind + sp_uparams ∉ inst_nuparams_indices *)
    All (ind_sp_uparams_notin (size_cxt + #|largs|)) inst_nuparams_indices ->
    lax |> size_cxt |arg+> arg_is_ind largs pos_indb inst_nuparams_indices

  | pos_arg_is_nested largs kname pos_ind u inst_uparams inst_nuparams_indices mdecl :
    lax = true ->
    (* ind + sp_uparams ∉ largs *)
    Alli ind_sp_uparams_notin size_cxt largs ->
    (* declared mdecl + pos_ind *)
    lookup_minductive E kname = Some mdecl ->
    pos_ind < #|PCUICEnvironment.ind_bodies mdecl| ->
    (* inst_uparams are positive *)
    All2 (fun x y =>
      (* fully applied ensured by typing*)
      (#|x.1| = cdecl_to_arity y.1)
      (* llargs are free *)
      * Alli (ind_sp_uparams_notin) (size_cxt + #|largs|) x.1
      (* args are pos lax or strict depending if you can nest or not *)
      * positive_argument y.2 (size_cxt + #|largs| + #|x.1|) x.2
    ) inst_uparams (rev (PCUICEnv_ind_uparams mdecl))
    ->
    (* ind + sp_uparams ∉ inst_nuparams_indices *)
    All (ind_sp_uparams_notin (size_cxt + #|largs|)) inst_nuparams_indices ->
    lax |> size_cxt |arg+> arg_is_nested largs (mkInd kname pos_ind) u
                              inst_uparams inst_nuparams_indices

  where "lax |> size_cxt |arg+> t " := (positive_argument lax size_cxt t) : type_scope.


  Inductive All2_param1 {A B R} (PR : forall a b, R a b -> Type) : forall {lA lB}, All2 R lA lB -> Type :=
  | All2_nil_param1 : All2_param1 PR (@All2_nil A B R)
  | All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                forall (r : R x y), PR _ _ r ->
                forall (al : All2 R l l'), All2_param1 PR al ->
                All2_param1 PR (All2_cons r al).

  Definition th_fonda_All2_param1 {A B R} PR (HPR : forall a b r, PR a b r) :
    forall lA lB (x : @All2 A B R lA lB), All2_param1 PR x.
  Proof.
    intros lA lB x. induction x; constructor.
    apply HPR. apply IHx.
  Defined.

  Definition positive_argument_rect'
    (P : forall {lax size_cxt arg}, positive_argument lax size_cxt arg -> Type)
    (P_arg_is_free :
        forall lax size_cxt (t : term) (i : ind_sp_uparams_notin size_cxt t),
        (* ------------------------ *)
        P (pos_arg_is_free lax size_cxt t i)
      )
    (P_arg_is_sp_uparams :
        forall lax size_cxt (largs : list term) (k : nat) (args : list term)
        (e : lax = true) (pos_k : k < #|uparams_b|)
        (is_sp : nth k (map snd (rev uparams_b)) false)
        (fapp : nth k (rev uparams_nb_args) 0 = #|args|)
        (notin_largs : Alli (fun (pos_arg : nat) (x : term) => ind_sp_uparams_notin pos_arg x) size_cxt largs)
        (notin_args : All (fun x : term => ind_sp_uparams_notin (size_cxt + #|largs|) x) args),
        (* ------------------------ *)
        P (pos_arg_is_sp_uparams lax size_cxt largs k args e pos_k is_sp fapp notin_largs notin_args)
      )
    (P_arg_is_ind :
        forall lax size_cxt (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term)
        (e : lax = true) (pos_ind : pos_indb < nb_block)
        (notin_largs : Alli (fun (pos_arg : nat) (x : term) => ind_sp_uparams_notin pos_arg x) size_cxt largs)
        (notin_args : All (fun x : term => ind_sp_uparams_notin (size_cxt + #|largs|) x) inst_nuparams_indices),
        (* ------------------------ *)
        P (pos_arg_is_ind lax size_cxt largs pos_indb inst_nuparams_indices
              e pos_ind notin_largs notin_args)
      )
    (P_arg_is_nested lax size_cxt :
        forall lax size_cxt (largs : list term) (kname : kername) (pos_ind : nat) (u : Instance.t)
        (inst_uparams : list (list term × argument)) (inst_nuparams_indices : list term)
        (mdecl : PCUICEnvironment.mutual_inductive_body)
        (e : lax = true)
        (notin_largs : Alli (fun (pos_arg : nat) (x : term) => ind_sp_uparams_notin pos_arg x) size_cxt largs)
        (ind_env_defined : lookup_minductive E kname = Some mdecl)
        (ind_pos_defined : pos_ind < #|PCUICEnvironment.ind_bodies mdecl|)
        (pos_nested :
            All2 (fun (x : list term × argument) (y : context_decl × bool) =>
              (#|x.1| = cdecl_to_arity y.1
              × Alli (fun (pos_arg : nat) (x0 : term) => ind_sp_uparams_notin pos_arg x0) (size_cxt + #|largs|) x.1)
              * (positive_argument y.2 (size_cxt + #|largs| + #|x.1|) x.2))
            inst_uparams (rev (PCUICEnv_ind_uparams mdecl)))
        (Ppos_nested : All2_param1 (fun x y r => P r.2) pos_nested)
        (notin_instance : All (fun x : term => ind_sp_uparams_notin (size_cxt + #|largs|) x) inst_nuparams_indices),
        (* ------------------------ *)
        P (pos_arg_is_nested lax size_cxt largs kname pos_ind u inst_uparams inst_nuparams_indices mdecl
              e notin_largs ind_env_defined ind_pos_defined pos_nested notin_instance)
      )
    : forall lax size_cxt arg (p : positive_argument lax size_cxt arg), P p.
  Proof.
    fix rec 3.
    intros ? ? ? p. destruct p as [ | | | ? ? ? ? ? ? ? ? ? ? ? pos_nested].
    - apply P_arg_is_free.
    - apply P_arg_is_sp_uparams.
    - apply P_arg_is_ind.
    - apply P_arg_is_nested.
      (* apply th_fonda_All2_param1. intros. apply rec. *)
      induction pos_nested; constructor; cbn.
      destruct x; destruct y; cbn.
      apply rec. apply IHpos_nested.
  Admitted.


  Definition positive_argument_strict {size_cxt arg} :
    positive_argument false size_cxt arg ->
    exists t, arg = arg_is_free t.
  Proof.
    intro k; inversion k.
    1: eauto.
    all : lia.
  Qed.


  (* A constructor is postive when:
     1. All of its arguments are positive
     2. The return indices do not contain the inductives nor the sp_uparams
  *)
  Definition positive_constructor (ctor : constructor_body) : Type :=
      Alli (positive_argument true) #|nuparams| ctor.(cstr_args)
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


(* Properties about positivity *)
Fixpoint pos_arg_inc {lax nb_block up pos_arg arg} k :
  positive_argument nb_block up pos_arg lax arg ->
  positive_argument (nb_block + k) up pos_arg lax arg.
Proof.
Admitted.

Fixpoint pos_ctor_inc {up nup ctor} k q :
  k <= q ->
  positive_constructor k up nup ctor ->
  positive_constructor q up nup ctor.
Proof.
Admitted.

Fixpoint pos_idecl_inc {nb_block up nup idecl} k :
  positive_one_inductive_body nb_block up nup idecl ->
  positive_one_inductive_body (nb_block + k) up nup idecl.
Proof.
Admitted.

Fixpoint pos_ctor_inc_le {up nup ctor} k q :
  k <= q ->
  positive_one_inductive_body k up nup ctor ->
  positive_one_inductive_body q up nup ctor.
Proof.
Admitted.

Fixpoint pos_idecl_inc_eq {nb_block up pos_arg idecl} k m :
  m = nb_block + k ->
  positive_one_inductive_body nb_block up pos_arg idecl ->
  positive_one_inductive_body m up pos_arg idecl.
Proof. intros ->. apply pos_idecl_inc. Qed.

Fixpoint lift_argument n above (t : argument) : argument :=
  match t with
  | arg_is_free t => arg_is_free (lift n above t)
  | arg_is_sp_uparam largs k args =>
      let largs' := mapi (fun i => lift n (i + above)) largs in
      let args' := map (lift n (#|largs| + above)) args in
      arg_is_sp_uparam largs' k args'
  | arg_is_ind largs pos_indb inst_nuparams_indices =>
      let largs' := mapi (fun i => lift n (i + above)) largs in
      let inst_nuparams_indices' := map (lift n (#|largs| + above)) inst_nuparams_indices in
      arg_is_ind largs' pos_indb inst_nuparams_indices'
  | arg_is_nested largs ind u inst_uparams inst_nuparams_indices =>
      let largs' := mapi (fun i => lift n (i + above)) largs in
      let inst_uparams' := map
        (fun '(llargs, arg) => ( mapi (fun i => lift n (i + #|largs| + above)) llargs,
                                 lift_argument n (#|llargs| + #|largs| + above) arg))
        inst_uparams in
      let inst_nuparams_indices' := map (lift n (#|largs| + above)) inst_nuparams_indices in
      arg_is_nested largs' ind u inst_uparams' inst_nuparams_indices'
  end.

Definition pos_lift_argument {lax nb_block up pos_arg } arg n :
  positive_argument nb_block up lax pos_arg arg ->
  positive_argument nb_block up lax (pos_arg + n) (lift_argument n 0 arg).
Proof.
Admitted.

Definition pos_lift_argument_eq {nb_block up pos_arg lax} arg n m :
  m = pos_arg + n ->
  positive_argument nb_block up lax pos_arg arg ->
  positive_argument nb_block up lax m (lift_argument n 0 arg).
Proof.
  intros ->. apply pos_lift_argument.
Qed.

End View.

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



(* View -> PCUIC.Env *)