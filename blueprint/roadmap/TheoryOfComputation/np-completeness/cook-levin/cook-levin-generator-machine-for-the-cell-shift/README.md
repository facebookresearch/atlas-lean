# Cook-Levin: generator machine for the cell-shift family

## [FAM] The family (pure specification)

- [Literals of an in-range shift clause](sh-lits.md)
- [Literals of an overflow clause](ov-lits.md)
- [Literals of a pushed-fill clause](pf-lits.md)
- [The shift block of a situation and a stack](sh-blk.md)
- [The cell-shift clause family](sh-family.md)
- [Well-formed situation tables for the cell-shift family](wf.md)
- [Coverage of target depths](depth-cover.md)
- [Bounds on in-range and overflow target depths](depth-disjoint.md)

## [FAM] The generator machine

- [Counters of the cell-shift generator](ck.md)
- [Base counters of literal positions](bs.md)
- [Counter holding a literal base](k.md)
- [Clause kinds of the cell-shift family](cl.md)
- [Number of literals of a cell-shift clause kind](nl.md)
- [Base counter of a literal](bs-2.md)
- [Constant offsets of the literals of a clause kind](cs.md)
- [Literal signs of a shift clause kind](sg.md)
- [Precomputation stages of the shift generator](ps.md)
- [Stages of the cell-shift literal routine](ls.md)
- [Setup and loop stages of a cell-shift block](st.md)
- [Loop-body stages of the cell-shift generator](bd.md)
- [Labels of the cell-shift generator](gl.md)
- [Entry label of a literal routine of the cell-shift generator](lit-l.md)
- [Label after a literal routine](after.md)
- [Entry label of the in-range chain](x-from.md)
- [Entry label of the pushed-fill chain](pf-from.md)
- [Label after a clause of the cell-shift generator](next-c.md)
- [Label of the decrement chain](sb-l.md)
- [Entry label of the situation chain](i-from.md)
- [Entry label of the stack chain of a situation](ik.md)
- [Labels of the shift generator](lab.md)
- [Constant offset of a literal in a block](csv.md)
- [Literal routine of the cell-shift generator](lit-p.md)
- [Block stages of the cell-shift generator](st-p.md)
- [Loop body of the cell-shift generator](bd-p.md)
- [The cell-shift generator](prog.md)
- [The cell-shift generator as a finite stack machine](sh-tm.md)

## [FAM] Clause kinds: literal positions

- [Literals of a clause kind at given positions](clits.md)
- [Increasing literal positions below a bound](mono.md)
- [Boundary before a literal](bnd.md)

## [FAM] Correctness: one literal, one clause

- [Empty scratch counters of the shift generator](rest.md)
- [One literal routine of the cell-shift generator](lit-run.md)
- [Per-literal step overhead of the cell-shift generator](lit-e.md)
- [Step bound for one clause](clause-b.md)
- [The literal routines of one clause of the cell-shift generator](lits-run.md)
- [One clause of the cell-shift generator](clause-run.md)

## [FAM] The shift and overflow clauses; the `x` chain; the decrement chain

- [First cell variable of a block](kbv.md)
- [Literal positions of an in-range shift clause](sh-pos.md)
- [Literal positions of an overflow clause](ov-pos.md)
- [Literal positions of a pushed-fill clause](pf-pos.md)
- [Counter state of a loop body](body.md)
- [The in-range chain of the cell-shift generator](xs-run.md)
- [The pushed-fill chain of the cell-shift generator](pf-run.md)
- [The decrement chain takes $n$ steps](sb-run.md)

## [FAM] Correctness: the two runtime loop bodies

- [Step bound for one in-range loop iteration](s-body-b.md)
- [Step budget of one overflow iteration of the cell-shift generator](o-body-b.md)
- [One iteration of the in-range loop of the cell-shift generator](sbody-run.md)
- [One iteration of the overflow loop of the cell-shift generator](obody-run.md)

## [FAM] Correctness: one `(i, k)` block, the label chains, the time loop, the generator

- [Counter state at the start of a block](blk.md)
- [Step budget for one block of the shift generator](ik-b.md)
- [Correctness of the shift generator on one block](ik-run.md)
- [Encoded blocks of one situation](blk-i.md)
- [Encoded blocks of one time step](blk-t.md)
- [Correctness of the shift generator on the stack chain of a situation](ks-run.md)
- [Correctness of the shift generator on the situation chain](is-run.md)
- [Step budget for one time step of the shift generator](t-body-b.md)
- [One iteration of the time loop of the shift generator](tbody-run.md)
- [Initial counter values of the shift generator](init-f.md)
- [Counters after the precomputation of the cell-shift generator](pre-f.md)
- [Cost of the precomputation of the cell-shift generator](pre-b.md)
- [Explicit time bound of the shift generator](sh-bound.md)
- [Correctness of the shift generator, with its explicit time bound](sh-run.md)

## [BOUND] The time bound is polynomial: `shBound ≤ shC · (T + H + 1)^6`

- [Time bound of the shift generator on uniform layouts](sh-bound-uni.md)
- [Constant of the shift-generator time bound](sh-c.md)
- [The shift-generator time bound as a polynomial](sh-poly.md)
- [Polynomial time bound for the shift generator](sh-time.md)
