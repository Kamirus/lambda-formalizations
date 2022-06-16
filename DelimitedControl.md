# Delimited-Control Operators

Delimited control is a computational effect that allows capture of delimited (or partial) continuations,
which contrasts with operations like `call/cc` that capture undelimited continuations,
meaning the whole context that surrounds the operation.

## Continuations / Contexts
The *continuation* is the *rest of the computation*, represented by the *context* of the current expression being evaluated.

e.g. consider an evaluation process of the following program: `(2 + f(3)) + 1`.

- To compute (2 + f(3)) + 1, we need to compute 2 + f(3) first,
- To compute  2 + f(3)     , we need to compute     f(3) first,
- Once we evaluate `f(3)`, we can *continue* with the *rest of the computation* that is (2 +) and then (+ 1),
- so the continuation can be written as `(2 + []) + 1` that is a program with one hole `[]` called a *context*.

Instead of a single operation like `call/cc`, delimited control is usually introduced using two operators, for example `shift/reset`:
- `shift` used to capture the (delimited) context; written as a binder `S f. e`
- `reset` used as a delimiter that restricts the part of the continuation to be captured; written with brackets `< e >`

## shift/reset
```
e ::= x | e e | λ x. e | S x. e | < e >
K ::= [] | K e | v K
T ::= [] | < K[T] >

(λ x. e) v      ~>  e [x := v]
< v >           ~>  v
< K [S f. e] >  ~>  < e [ f := λ x. < K[x] > ] >

    e    ~>     e'
-------------------- (eval)
K[T[e]] --> K[T[e']]
```

The 3rd contraction (~>) rule describes the semantic interaction between the two operators
where the context `K` delimited by the inner-most `reset` gets captured and bound to `f` as a lambda.

Note that:
- the evaluation context `K` does not cross the `reset` boundary, meaning we won't go under a delimiter (`reset`) when plugging a term,
- whereas the context `K[T]` is an evaluation context that *may* cross the `reset` boundary, and it's used in the single (eval) rule that defines the evaluation.

### Example
Consider the following program (assuming we've extended the calculus with numbers and (+))

`1 + < 2 + (S f. 3 + f (f 4)) >`

Which after one (eval) step is:

`1 + < 3 + f (f 4) >` where `f = λ x. < 2 + x >`

And finally computes to an equivalent of `1 + 3 + 2 + 2 + 4`


## Operator Variations

Notice that `reset` (<>) occurs twice in the result of the 3rd contraction rule:
- outer `reset` keeps the outer context from being captured during evaluation ("reset makes any piece of code appear pure to the outside, that is, devoid of control effects")
- inner `reset` makes the captured continuation pure

There are variations that drop either one of these delimiters:
- The `control` operator; written as a binder `C f. e`; drops the inner delimiter
- and two other operators `shift0` (S₀ f. e) and `control0` (C₀ f. e) that also drop the outer delimiter

```
< K [S  f. e] >  ~>  < e [ f := λ x. < K[x] > ] >
< K [C  f. e] >  ~>  < e [ f := λ x.   K[x]   ] >
< K [S₀ f. e] >  ~>    e [ f := λ x. < K[x] > ]
< K [C₀ f. e] >  ~>    e [ f := λ x.   K[x]   ]
```

> These variations are usually studied separately and in literature are referred to as:
> 
> `shift/reset`, `control/prompt` and `shift0/reset0`, `control0/prompt0`

### Example: shift vs control
```
< let x = S f. 1 + f 2 in S g. x > --> < 1 + (λ x. < S g. x >) 2 > --> < 1 + < S g. 2 > > --> < 1 + < 2 > > -->* 3
< let x = C f. 1 + f 2 in C g. x > --> < 1 + (λ x.   C g. x  ) 2 > --> < 1 +   C g. 2   > --> <       2   > -->* 2
```

## Macro-expressivity Between Variations

TODO

## Source
https://homes.luddy.indiana.edu/ccshan/recur/recur.pdf
