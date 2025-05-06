
# Notes
-> passer en context pour les arguments ???

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
