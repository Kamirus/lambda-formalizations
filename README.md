# Lambda Calculi Formalizations

- **Simply Typed Lambda Calculus**
  - [Term representation using Nested Datatypes](Terms.v)
    - [Progress and Preservation](STLC_Generic.v)
  - [Legacy: Type-Level de Bruijn indices](stlc.v) (unnecessarily difficult approach)
- **Delimited-Control Operators shift0/dollar**:
  - **Contribution**:
    - Formalize `λ$` calculus with its **evaluation** strategy
    - Introduce an **evaluation** strategy for `λc$` (a fine-grained version of `λ$`)
    - Define **similarity** relations to prove **correspondance** between both calculi in a form of **simulations** which state that: *similar terms compute to similar values*
  - [`λ$` calculus](LambdaDollar.v) (paper reference: [section 2.2](https://ii.uni.wroc.pl/~dabi/publications/APLAS12/materzok-biernacki-aplas12.pdf))
  - [`λc$` calculus: a Fine-Grained version of `λ$`](LambdaLetDollar.v) (paper reference: [Figure 1](https://dl.acm.org/doi/10.1145/3479394.3479399))
  - Correspondence between `λ$` and `λc$`:
    - [Simulation: `λ$` to `λc$`](LambdaDollarToLet.v)
    - [Simulation: `λc$` to `λ$`](LambdaLetToDollar.v)

Create Makefile with `coq_makefile -f _CoqProject *.v -o Makefile`


## Future Work
- Examine the potential of supporting the `control0` operator for the current evaluation strategy
- Develop the alternative evaluation strategy - the hybrid (reduces differently when under the delimiter) one that aggressively duplicates `$`
  - Simplify both calculi to the most common format to showcase the fine-grained difference - single term-tree `tm A`, two different reductions
  - Remove call-by-value nature from both, let let-bindings do the rest
  - Explore a different similarity relation strategy - instead of substituting similar terms try to work on common skeletons (`tm A`) with a substitution (`A → val`) of similar values
