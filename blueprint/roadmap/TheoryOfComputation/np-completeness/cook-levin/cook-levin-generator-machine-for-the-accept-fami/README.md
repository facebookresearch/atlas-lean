# Cook-Levin: generator machine for the accept family

## The family (pure specification)

- [Literals of an accept code clause](code-lits.md)
- [Literals of an accept cell clause](cell-lits.md)
- [The accept family of a layout](acc-fam.md)

## The generator machine

- [Counters of the accept generator](ck.md)
- [Clause kinds of the accept generator](ak.md)
- [Base counter of an accept clause](bc.md)
- [Offset of a clause's literal](off.md)
- [Polarity of an accept clause's literal](sg.md)
- [Precomputation stages of the accept generator](ps.md)
- [Stages of the accept generator's literal routine](ls.md)
- [Labels of the accept generator](gl.md)
- [Entry label of an accept code clause](code-from.md)
- [Start of the accept code chain](code-start.md)
- [Entry label of an accept cell clause](cell-from.md)
- [First clause label of the accept generator](start.md)
- [Next label after a clause of the accept generator](next-c.md)
- [Literal routine of the accept generator](lit-p.md)
- [Generator machine for the accept family](prog.md)
- [The accept generator as a finite multi-stack machine](acc-tm.md)

## Correctness: one clause

- [Empty scratch counters of the accept generator](rest.md)
- [Run of the literal routine of the accept generator](lit-run.md)
- [Step bound for one accept clause](clause-b.md)
- [One clause of the accept generator](clause-run.md)

## Correctness: the two label chains and the whole generator

- [Run of the code-clause chain of the accept generator](codes-run.md)
- [Run of the accept cell chain](cells-run.md)
- [Initial counters of the accept generator](init-f.md)
- [Counters after the precomputation of the accept generator](pre-f.md)
- [Cost of the precomputation of the accept generator](pre-b.md)
- [Explicit time bound of the accept generator](acc-bound.md)
- [Run of the accept generator's precomputation](pre-run.md)
- [Correctness of the accept generator, with its explicit time bound](acc-run.md)

## The time bound is polynomial

- [The accept generator's time bound on the uniform layout](acc-bound-uni.md)
- [Constant of the accept generator's time bound](acc-c.md)
- [Polynomial time bound of the accept generator](acc-time.md)

## Link to the semantic accept family

- [The concrete accept family is a layout-level accept family](acc-family-eq.md)
- [Time bound of the accept generator for a concrete machine](acc-gen-time.md)
