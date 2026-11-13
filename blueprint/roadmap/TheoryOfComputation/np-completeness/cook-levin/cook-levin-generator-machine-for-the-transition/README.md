# Cook-Levin: generator machine for the transition clause families

## Draft C3 variable layout

- [Variable layout of the transition clauses](layout.md)
- [Variables per time step](row-w.md)
- [Number of variables of the transition-clause formula](num-vars.md)
- [Index of a label/state variable](x-idx.md)
- [Index of a cell variable in the transition-family layout](c-idx.md)
- [Number of literals of a transition clause](n-lits.md)

## The clause family (pure specification)

- [Position of a literal in a transition clause](lit-pos.md)
- [Literals of a transition clause](lits.md)
- [Dense clause from a list of literals](dense-clause.md)
- [The transition clause family](family.md)

## Block decomposition of a dense clause

- [Gap encoding of a dense clause](gap-enc.md)
- [Increasing literal positions](inc.md)
- [Lowering the lower bound keeps a literal list increasing](mono-lo.md)
- [Encoding a dense clause block by block](encode-clause-dense-clause.md)
- [Shifting the start of a gap encoding](gap-enc-shift.md)

## The literal positions are strictly increasing

- [Successor of a number with a non-maximal remainder](div-mod-succ-of-lt.md)
- [Increasing literal sequences](inc-of-mono.md)
- [Well-formed situation tables for the transition clauses](wf.md)

## The generator machine

- [Counters of the transition-family generator](ck.md)
- [Stacks of the clause-family generator](gk.md)
- [Stack alphabets of the generator](g.md)
- [Stages of the transition-clause generator's precomputation](ps.md)
- [Stages of the transition-clause generator's literal routine](ls.md)
- [Labels of the clause-family generator](gl.md)
- [Entry label of a literal routine (transition-clause generator)](lit-l.md)
- [Label after a literal routine in the transition-family generator](after.md)
- [Entry label of the clause routine for situation $i$](sit-l.md)
- [Label after a situation clause in the transition-family generator](after-s.md)
- [Stack index of a literal in a transition clause](k-a.md)
- [Row offset of a literal in a transition clause](k-b.md)
- [Constant offset of a literal position](cst.md)
- [Polarity of a transition-clause literal](sgn.md)
- [Literal routine of the transition-clause generator](lit-p.md)
- [Generator machine for the transition clause families](prog.md)
- [The clause-family generator as a finite stack machine](gen-tm.md)

## Correctness: one literal

- [Scratch counters at rest in the clause-family generator](rest.md)
- [Run of one literal routine (transition-clause generator)](lit-run.md)

## Correctness: one clause

- [Boundary before a literal of a transition clause](bnd.md)
- [Resting counter values in the transition-family time loop](base.md)
- [Per-literal time bound of the transition-clause generator](lit-e.md)
- [Step bound for one clause of the transition-family generator](clause-b.md)
- [Run of the literal routines of a clause (transition-clause generator)](lits-run.md)
- [Run of the transition-family generator on one clause](clause-run.md)

## Correctness: situations, time steps, the whole generator

- [Encoded transition clauses of one time step](blk.md)
- [Time-loop invariant of the transition-family generator](loop-p.md)
- [Step bound for one time-loop iteration of the transition-family generator](body-b.md)
- [Step bound for the transition-clause generator's precomputation](pre-b.md)
- [Time bound of the generator](gen-bound.md)
- [One iteration of the time loop](time-body.md)
- [Generator output after part of the time loop](out-after.md)
- [Initial counters of the transition-clause generator](init-f.md)
- [Correctness of the clause-family generator, with its explicit time bound](gen-run.md)
- [Correctness of the clause-family generator](gen-correct.md)

## The time bound is polynomial: `genBound ≤ genC · (T + H + 1)^5`

- [Uniform layout](uni.md)
- [Uniform bound on the generator's time](gen-bound-uni.md)
- [Constant of the generator's time bound](gen-c.md)
- [Time-bound polynomial of the clause-family generator](gen-poly.md)
- [Polynomial time bound for the clause-family generator](gen-time.md)
