Set Primitive Projections.

(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
(* From MetaRocq.Common Require Import BasicAst Primitive Universes Environment. *)
(* From Equations.Prop Require Import Classes EqDecInstances. *)
(* From Coq Require Import List. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICOnFreeVars PCUICInstDef PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICSigmaCalculus PCUICInstConv.
Import PCUICEnvironment.

(* Todo list:

[ ] 1. Finish Proof with triv indices
[ ] 2. Split the files
[ ] 3. Finish the proofs
[ ] 4. Adapt the usual pos cdt + view
[ ] 5. Fix metarocq
[ ] 6. Figure out issues indices and indictuve-inductive

*)

Definition map_rev [A B : Type] (f : A -> B) (l : list A) :
  map f (rev l) = rev (map f l).
Proof.
Admitted.

Definition All_rev (A : Type) (P : A -> Type) (l : list A) :
  All P l -> All P (rev l).
Proof.
Admitted.


Axiom todo_ : forall {A}, A.
#[warn(note="TO IMPLEMENT")] Notation todo := todo_.

Axiom todot_ : forall {A}, string -> A.
#[warn(note="TO IMPLEMENT")] Notation todot x := (todot_ x).

Ltac cbn_length := repeat (rewrite ?length_app ?length_map ?List.length_rev ?length_rev ?mapi_length ?mapi_rec_length);
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










(* *** Simplified Def of Inductive Types *** *)

(* An argument is either:
  - a term t that does not contain the ind nor the sp_uparams
  - of the form (∀ x1 ... xn, A / Ind i / tInd ...
*)
(* Unset Elimination Schemes. *)

Inductive argument : Type :=
| arg_is_free      (t : term)
| arg_is_sp_uparam (largs : list term) (k : nat) (args : list term)
| arg_is_ind       (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term)
| arg_is_nested    (largs : list term) (ind : inductive) (u : Instance.t)
                    (inst_uparams : list (list term * argument)) (inst_nuparams_indices : list term).


(* Fixpoint argument_rect (P : argument -> Type)
  (Harg_is_free : (forall t : term, P (arg_is_free t)))
  (Harg_is_sp_uparam : forall (largs : list term) (k : nat) (args : list term),
    P (arg_is_sp_uparam largs k args))
  (Harg_is_ind : forall (largs : list term) (pos_indb : nat) (inst_nuparams_indices : list term),
    P (arg_is_ind largs pos_indb inst_nuparams_indices))
  (Harg_is_nested : forall (largs : list term) (ind : inductive) (u : Instance.t)
    (inst_uparams : list argument)(pos_inst_uparams : All P inst_uparams)
    (inst_nuparams_indices : list term),
    P (arg_is_nested largs ind u inst_uparams inst_nuparams_indices))
  (a : argument) : P a.
Proof.
  destruct a.
  - now apply Harg_is_free.
  - now apply Harg_is_sp_uparam.
  - now apply Harg_is_ind.
  - apply Harg_is_nested. induction inst_uparams; constructor.
    apply argument_rect; eauto. apply IHinst_uparams.
Qed. *)

(* Set Elimination Schemes. *)





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
  ind_relevance : relevance }.



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
  ind_variance : option (list Universes.Variance.t) }.

  (* ind_npars : nat ===>> computed  *)
  (* ind_params : context; => split in ind_uparams and ind_nuparams *)



(* functions on arguments *)
Fixpoint argument_to_term (nb_block : nat) (pos_arg : nat) (arg : argument) {struct arg} : term :=
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


Axiom (mutual_to_view : PCUICEnvironment.mutual_inductive_body -> mutual_inductive_body).
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


  Definition ind_sp_uparams_notin_tLambda (k : nat) (l : list term) (t : term) :
    Alli (ind_sp_uparams_notin) k l ->
    ind_sp_uparams_notin (k + #|l|) t ->
    ind_sp_uparams_notin k (it_tLambda l t).
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
    pos_ind < #|ind_bodies (mutual_to_view mdecl)| ->
    (* inst_uparams are positive *)
    All2 (fun x y =>
      let llargs := x.1 in let arg := x.2 in
      let cdecl  := y.1 in let pos := y.2 in
      (* fully applied ensured by typing*)
      (#|llargs| = cdecl_to_arity cdecl)
      (* llargs are free *)
      * Alli (ind_sp_uparams_notin) (size_cxt + #|largs|) llargs
      (* args are pos lax or strict depending if you can nest or not *)
      * positive_argument pos (size_cxt + #|largs| + #|llargs|) arg
    ) inst_uparams (rev (ind_uparams (mutual_to_view mdecl)))
    ->
    (* ind + sp_uparams ∉ inst_nuparams_indices *)
    All (ind_sp_uparams_notin (size_cxt + #|largs|)) inst_nuparams_indices ->
    lax |> size_cxt |arg+> arg_is_nested largs (mkInd kname pos_ind) u
                              inst_uparams inst_nuparams_indices

  where "lax |> size_cxt |arg+> t " := (positive_argument lax size_cxt t) : type_scope.

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
    * Alli (sp_uparams_notin) #|nuparams| (map decl_type (rev indb.(ind_indices))).

End PositiveIndBlock.

Definition positive_mutual_inductive_body (mdecl : mutual_inductive_body) : Type :=
    Alli (ind_sp_uparams_notin mdecl.(ind_uparams)) 0 (terms_of_cxt mdecl.(ind_nuparams))
  * All (positive_one_inductive_body #|mdecl.(ind_bodies)| mdecl.(ind_uparams)
        mdecl.(ind_nuparams)) mdecl.(ind_bodies).


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


  (* lemma for binders *)
  Definition ind_sp_uparams_notin_tProd uparam k l t :
    Alli (ind_sp_uparams_notin uparam) k l ->
    ind_sp_uparams_notin uparam (k + #|l|) t ->
    ind_sp_uparams_notin uparam k (it_tProd l t).
  Proof.
  Admitted.


  Definition ind_sp_uparams_notin_tLambda_eq uparam k l t m :
    m = k + #|l| ->
    Alli (ind_sp_uparams_notin uparam) k l ->
    ind_sp_uparams_notin uparam m t ->
    ind_sp_uparams_notin uparam k (it_tLambda l t).
  Proof.
  Admitted.

  Definition ind_sp_uparams_notin_mkApps uparam k u vs :
    All (ind_sp_uparams_notin uparam k) vs ->
    ind_sp_uparams_notin uparam k u ->
    ind_sp_uparams_notin uparam k (mkApps u vs).
  Proof.
  Admitted.







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
  (* largs, args : updated arg to sub [∀ largs, A_k args]
     llargs, arg : updated instantiation [λ llargs, arg]
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
    | arg_is_nested _ _ _ _ _ =>
        todot "fix nested first"
    end.

  Definition pos_sub_uparams pos_sub_cxt largs args (lax : bool) (llargs : list term) (arg : argument)
    (* contet substitution *)
    (pos_largs : Alli (ind_sp_uparams_notin g_uparams_b) (nb_cxt_sub + pos_sub_cxt) largs)
    (pos_args  : All  (ind_sp_uparams_notin g_uparams_b  (nb_cxt_sub + pos_sub_cxt + #|largs|)) args)
    (* arg to substitute by *)
    (* WARNING: Check pos *)
    (fapp_arg : #|llargs| = #|args|)
    (pos_llargs : Alli (ind_sp_uparams_notin g_uparams_b) (nb_cxt_sub + pos_sub_cxt + #|largs|) llargs)
    (pos_arg : positive_argument nb_m_block g_uparams_b lax (nb_cxt_sub + #|llargs| + pos_sub_cxt + #|largs|) arg)
    :
    positive_argument nb_m_block g_uparams_b lax
      (nb_cxt_sub + pos_sub_cxt) (sub_uparam largs args llargs arg).
  Proof.
    induction pos_arg; cbn.
    + apply pos_arg_is_free. apply ind_sp_uparams_notin_tProd => //.
      apply ind_sp_uparams_notin_mkApps => //.
      eapply ind_sp_uparams_notin_tLambda_eq; tea.
      1: solve_length.
    + eapply pos_arg_is_sp_uparams => //.
      - cbn_length => //.
      - apply Alli_app_inv => //. eapply Alli_mapi. 2: apply a.
        intros j x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all: solve_length.
      - cbn_length. eapply All_map. 2: apply a0. cbn.
        intros x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all: solve_length.
    + apply pos_arg_is_ind => //; cbn_length.
      - apply Alli_app_inv => //. eapply Alli_mapi. 2: apply a.
        intros j x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all: solve_length.
      - cbn_length. eapply All_map. 2: apply a0. cbn.
        intros x H. eapply ind_sp_uparams_notin_subst_rev_eq.
        3: apply pos_args. 3: apply H.
        all: solve_length.
    + admit.
      (* fix nested first *)
  Admitted.

  Definition err_arg : list term * argument
    := ([], arg_is_free (tVar "impossible case")).

  (* Specialize an argument
  1. If it is a strpos uparams => substite by its instantiation
  2. Otherwise propagate the instantiation  *)
  Definition specialize_argument (pos_sub_cxt : nat) (arg : argument) : argument :=
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
    (* Careful => also need to add indices for type checking *)
    | arg_is_ind largs i args =>
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams]) largs pos_sub_cxt in
        let args'  := map (fun t => t.[up (pos_sub_cxt + #|largs|) inst_uparams]) args in
        arg_is_ind largs' (i + nb_g_block) args'
    | arg_is_nested largs ind u insta_uparams inst_nuparams_indices =>
        let largs' := mapi_rec (fun i t => t.[up i inst_uparams]) largs pos_sub_cxt in
        let insta_uparams' := todot "to update" in
        (* let insta_uparams' := map (specialize_argument (pos_sub_cxt + #|largs|)) insta_uparams in *)
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
      1: lia.
      1: { intros n x H. rewrite Nat.add_comm. unfold ind_sp_uparams_notin.
            rewrite -shiftnP_add. rewrite -{1}(Nat.add_0_r (nb_l_nuparams + pos_arg +
            #|largs|)). apply on_free_vars_lift_impl. rewrite shiftnP_add; cbn.
            exact H.
      }
      rewrite -Hfst. apply All_nth => //. 1: rewrite size_inst_uparams; lia.
      apply positive_inst_llargs.
    - unshelve eapply pos_lift_argument_eq.
      * exact (nb_cxt_sub + #|llargs|).
      * lia.
      (* the arguments we subtitute is positive ???*)
      * rewrite -Hfst -Hsnd. apply All_nth => //. 1: rewrite size_inst_uparams; lia.
        admit.
  + apply pos_arg_is_ind.
    - reflexivity.
    - lia.
    - apply Alli_notin_eq => //. lia.
    - apply All_notin_eq => //. solve_length.
  + apply pos_arg_is_nested with (mdecl := mdecl).
    - reflexivity.
    - admit.
    - assumption.
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
        rewrite nb_new_args_unfold; lia.
    (* pos indices *)
    + rewrite length_app nb_new_args_unfold ! mapi_length.
      apply All_app_inv.
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
    - admit. (* issue => too much g_args *)
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
          let new_arg := arg_is_ind largs (pos_indb + nb_g_block + #|acc_indb|) todo in
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
      repeat constructor => //; try lia.
      admit. (* new indices -> to solve *)
    + apply All_app_inv; only 1: (eapply All_impl; tea; intros; apply pos_idecl_inc) => //.
      eapply All_map; [| apply pos_l_indb ].
      intros idecl. apply pos_specialize_idecl => //.
      (* * assumption. move => //. eapply Alli_impl; [ easy | auto using pos_arg_inc ]. *)
      eapply All2_impl; tea. intros [llargs arg] [cdecl pos] [[fapp pos_llargs] pos_arg].
      cbn in *. repeat split; tea. apply pos_arg_inc => //.
  Admitted.

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
          intros; eapply pos_ctor_inc; tea.
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
          intros; eapply pos_ctor_inc_le; tea.
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