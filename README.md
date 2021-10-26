![logo](planet.png)

# SATurne

*A purely functional verified SAT solver which produces proofs*

**SATurne** is a simple purely functional SAT solver written and verified in [Coq](https://coq.inria.fr/). It's a tiny solver absolutely not designed for performances nor scalability. It is, however, intended to be well-documented, easy to understand and extremely trustworthy.

**SATurne** is progressively integrated as the SAT solver behind the [Modulus](https://github.com/jdrprod/Modulus) SMT solver.

## Few words on SATurn design

At it's core, **SATurne** is a ridiculously simple solver very similar to the one described in
[this article](https://web.archive.org/web/20201109101535/http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html).

## Features

**SATurne** is not only a solver. It is also a collection of Coq theories formalizing the boolean logic and the associated proof systems (e.g. the resolution system).

**SATurne** is shipped with a proof checker to check proofs of unsatisfiability based on the resolution system. This checker is proven to be correct and can be extracted to a self contained OCaml module.

Since SATurne solve only formulas in clausal form, it also features a verified CNF converter.

## Coq Sources

The sources are located in the `src` folder. A `_CoqProject` and a makefile are provided. Simply type `make` at the project root SATurne is ready to be loaded in your favorite Coq editor.

### Structure/TODOs

```
src/
  Clauses.v     -> Theories of literals, clauses and set of clauses
  Cnf.v         -> conversion into cnf
  Proof.v       -> proof checker
  Evaluation.v  -> (old) models in boolean logic
  Sat.v         -> (old) facts about satisfiability
  Solver_aux.v  -> (old) useful facts used to prove the solver
  Solver.v      -> (old) verified solver
```