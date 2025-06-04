# 3 approahces
-> projection (dep)
-> inst_to_terms + eq (no dep)
-> fct + eq (no dep)

# Notes ajout condition

  This must be well-formed:

    ↓↓g_args ,,, ↓g_largs ,,,  (↓σ)(l_nuparams ,,, indices)



    1. rc_notin args
    2. rc_notin largs
    3. σ must **not** well-formed, but its subtitution yes.
       As isup_notin (l_nuparams ,,, indices) => only care about not-isup
       (bit more flexible)

  "INFORMAL ARGUMENT" => if RC ∈ t, and t : T => isup ∈ T

    σ = σ1 ∪ σ2
    σ1 = nest on => do not ask that isup ∉ T
    σ2 = not nest on => ask isup ∉ T

    Addition of 2. and 3. to positivity forces us to prove it in
    1. sub_uprams:
        the instantiation to substitute is nested => get sth nested i.e. stuff to prove
        needed it for uparams case
    2. specialize_argument:

        forall (i : nat) (x : term),
        rc_notin_bool (map check_lax Γ) (i + nb_binders) x ->
        rc_notin_bool (map check_lax (args ++ l_args + nuparams ++ mapi_rec specialize_argument Γ nb_l_nuparams))
        (i + nb_binders) x.[up (i + (nb_l_nuparams + #|Γ| + nb_binders)) inst_uparams]

    should work, no ?
    args true peut venir que de σ:
    opt 1. => rc_notin σ donc ok => prendre just args_no_rc ? => vie plus simple
    ? opt 2. => isup notin ? => σ not isup => rc_notin donc ok


1. is check_lax arg = true -> rc_notin ok ?
2. Do I really needs to extra-conditions ?
3. What about cstr_extra_args needing to be false ?
4. Prove the subst lemma ?





-> Pbl nom dans le fichier => wrap in a module ???
  => Section strengthening => "Prop are preserved"
  => Section with the proofs

-> how to deal with sub ok ?
-> proof convoluted
-> use forallb etc... to get a function easily

-> All_map + impl rather than All_map


Sec 2: Issues -> rec
Sec 3: intuitive + solutions
Sec 4: more technical
Sec 5: more technical

# Notes

# Changes

## PCUICViewInductive

Concept:
-> uparams explicit, could with nb but may as well
-> split size_cxt => nb_nup + #|Γ| + nb_binders
-> cstr => **All_fold ? (rev) !!!** (dep args)

Practical:
-> change lift arguments split Γ in 2
-> relation pos_arg_notin fold and unfold

## PCUICNestedToMutual

Concept:
-> no changes to function
-> issue is lift_argugment ?
-> Reason about All_fold ???


Practical:
-> Spe Arg:
  -> lift arg case of spec_arg is **more** involved
  -> need solve_length to link Γ to nΓ

# Example thiago

Foo :=
| c : x, y : All foo (fun _ => True) [x,y] -> foo