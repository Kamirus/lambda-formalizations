# Simply Typed Lambda Calculus Formalization

[stlc.v](stlc.v)

Create Makefile with `coq_makefile -f _CoqProject *.v -o Makefile`


## Notes

- usual lambda cbn vs cbv, try to tie both computations using better ~ relation
- λc$ has normalization redution (can go under binders), using `C` red. context can go inside
- λ$ has evaluation (CBV, only to whnf)
- End goal:
  - create an evaluation relation for λc$
  - relate computations in λc$ and λ$ now with both having evaluation relation
  - optionally add `let` and change `S0` from a binder to combinator in λ$ so that we don't have to translate between both languages - less not interesting problems 

## Questions
