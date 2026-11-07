# Cook-Levin: the cell one-hot family

## [FAM] The family (pure specification)

- [At-least-one literals of a cell](alo-lits.md)
- [At-most-one literals for a pair](amo-lits.md)
- [At-most-one clauses of the first rows of a cell](rows-cnf.md)
- [One-hot clauses of a cell](cell-cnf.md)
- [The one-hot cell family](oh-family.md)

## [FAM] The generator machine

- [Counters of the one-hot generator](ck.md)
- [Clause kinds of a one-hot cell](cl.md)
- [Number of literals of a one-hot clause kind](nl.md)
- [Offset of a literal in a one-hot clause](off.md)
- [Literal sign of a clause kind](sg.md)
- [Well-formed clause kinds](wf.md)
- [Stages of the one-hot precomputation](ps.md)
- [Stages of the one-hot literal routine](ls.md)
- [Control labels of the one-hot generator](gl.md)
- [Entry label of a one-hot literal routine](lit-l.md)
- [Label after a literal routine of the one-hot generator](after.md)
- [Entry label of an at-most-one clause](pr.md)
- [Entry label for the first rows of a cell](y-done.md)
- [One-hot generator: the label after a clause](next-c.md)
- [One-hot generator: the routine for one literal](lit-p.md)
- [The one-hot generator](prog.md)
- [The one-hot generator as a finite multi-stack machine](oh-tm.md)

## [FAM] Clause kinds: literal positions

- [Literals of a one-hot clause kind](clits.md)
- [Boundary before a literal of a cell clause](bnd.md)

## [FAM] Correctness: one literal, one clause

- [Empty scratch counters of the one-hot generator](rest.md)
- [Run of one literal routine (one-hot generator)](lit-run.md)
- [Per-literal step cost of the one-hot generator](lit-e.md)
- [Step budget for one one-hot clause](clause-b.md)
- [Run of the literal routines of a clause (one-hot generator)](lits-run.md)
- [One clause of the one-hot generator](clause-run.md)

## [FAM] Correctness: the clauses of one cell (a 2-D label chain)

- [Generator run over one row of at-most-one clauses](row-run.md)
- [Generator run over the first rows and the at-least-one clause](rows-run.md)
- [Step bound for one cell](cell-b.md)
- [Generator run for one cell](cell-run.md)

## [FAM] Correctness: the three nested runtime loops and the whole generator

- [Encoded one-hot clauses of one stack at one time step](blk-k.md)
- [Encoded one-hot clauses of one time step](blk-t.md)
- [Step budget for one stack iteration of the one-hot generator](k-body-b.md)
- [One stack iteration of the one-hot generator](kbody-run.md)
- [Step budget for one time step of the one-hot generator](t-body-b.md)
- [Generator run over one time step](tbody-run.md)
- [Initial counters of the one-hot generator](init-f.md)
- [Counter values after the one-hot precomputation](pre-f.md)
- [Step budget of the one-hot precomputation](pre-b.md)
- [Explicit time bound of the one-hot generator](oh-bound.md)
- [Correctness of the one-hot generator, with its explicit time bound](oh-run.md)

## [BOUND] The time bound is polynomial: `ohBound ≤ ohC · (T + H + 1)^6`

- [Time bound of the one-hot generator on a uniform layout](oh-bound-uni.md)
- [Constant of the one-hot time bound](oh-c.md)
- [The one-hot time bound as a polynomial](oh-poly.md)
- [Polynomial time bound for the one-hot generator](oh-time.md)
