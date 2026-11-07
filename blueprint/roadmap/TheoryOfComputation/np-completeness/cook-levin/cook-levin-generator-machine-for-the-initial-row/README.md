# Cook-Levin: generator machine for the initial-row family

## An input stack beside a counter machine

- [Stacks of a counter machine with an input stack](ik.md)
- [Alphabets of a counter machine with an input stack](i.md)
- [Stacks of a counter machine with an extra input stack](emb.md)
- [The counter stacks inside the generator's stacks](lift-e.md)
- [Run lifting](run-lift.md)

## Reading one input symbol into the label

- [Read test for one code](rd-s.md)
- [The read chain](read-run.md)

## The family (pure specification)

- [Empty-cell variable of the initial row](z-b.md)
- [Start-code clause of the initial row (I1)](i-code.md)
- [Row-0 clauses for the other stacks](i-other.md)
- [Input clauses of the initial row (I3)](i-in.md)
- [Certificate clauses of the initial row (I4)](i-cert.md)
- [Row-0 prefix clauses](i-pre.md)
- [Row-0 tail clauses](i-tail.md)
- [The init family](init-fam.md)

## The generator machine

- [Counters of the initial-row generator](ck.md)
- [Loop phases of the initial-row generator](ph.md)
- [Loop-count counter of a phase (initial-row generator)](c-n.md)
- [Base counter of a phase (initial-row generator)](c-z.md)
- [Clause kinds of the initial-row generator](cl.md)
- [Number of literals of a clause kind](nl.md)
- [Literal offsets](off.md)
- [Literal signs of an init-family clause kind](sg.md)
- [Base counter of a clause kind (initial-row generator)](bc.md)
- [Labels of the first precomputation part](ps1.md)
- [Labels of the second precomputation part](ps2.md)
- [Stages of the literal routine (initial-row generator)](ls.md)
- [Labels of the initial-row generator](gl.md)
- [Entry label of a literal routine (initial-row generator)](lit-l.md)
- [Label after a literal routine (initial-row generator)](after.md)
- [Label after a phase loop](next.md)
- [Label after a clause](next-c.md)
- [The first read test](rd0.md)
- [Label after a failed read test](miss.md)
- [Labels of the initial-row generator for a layout](lb.md)
- [The literal routine of the initial-row generator](lit-p.md)
- [The counter part of the initial-row generator](prog.md)
- [The initial-row generator](iprog.md)
- [The init generator as a finite multi-stack machine](init-tm.md)

## Clause kinds: literal positions

- [Literals of a clause kind](clits.md)
- [Well-formed init-family clause kinds](wf.md)
- [Boundary before a literal (initial-row generator)](bnd.md)
- [Literals of a clause kind in range](in-r.md)

## Correctness: one literal, one clause (in the counter part)

- [Empty scratch counters](rest.md)
- [Run of one literal routine (initial-row generator)](lit-run.md)
- [Per-literal step cost of the initial-row generator](lit-e.md)
- [Step bound for one clause (initial-row generator)](clause-b.md)
- [Run of the literal routines of a clause (initial-row generator)](lits-run.md)
- [Run of one clause (initial-row generator)](clause-run.md)

## Correctness: the five phase loops (counter part)

- [Step bound for one loop iteration (initial-row generator)](body-b.md)
- [One phase-loop iteration of the initial-row generator](body-run.md)
- [One phase loop](phase-run.md)
- [Counter part of one I3 iteration](i3pre-run.md)

## Correctness: the I3 loop (reads the input; in the extended machine)

- [The I3 loop](i3-run.md)

## Positions, and the machine's blocks are the family's clauses

- [Row-0 cells fit in the variable range](qpos.md)
- [Concatenating consecutive blocks of indices](flat-blocks.md)

## Precomputation and the whole generator

- [Initial counters of the init generator](init-f.md)
- [Counters after the precomputation](pre-f.md)
- [Step bound for the precomputation](pre-b.md)
- [Run of the precomputation (initial-row generator)](pre-run.md)
- [The I3 loop on the whole input](i3-full.md)

## The whole generator

- [Step bound of one phase loop (initial-row generator)](loop-b.md)
- [Time bound of the init generator](init-bound.md)
- [Correctness of the init generator, with its explicit time bound](init-run.md)

## The time bound is polynomial

- [Time bound of the init generator at uniform parameters](init-bound-uni.md)
- [Constant of the init generator's time bound](init-c.md)
- [Polynomial time bound for the init generator](init-time.md)

## Link to the semantic initial-row family (I4 sorted and deduplicated)

- [Lookup in an all-positive literal list](lookup-pos.md)
- [Dense clauses of positive literals depend only on their positions](dense-clause-congr.md)
- [Sorted certificate code list](ycs.md)
- [Codes of input symbols](enc-f.md)
- [The init family of an encoding is a layout-level init family](init-family-eq.md)
- [Time and output of the init generator for an encoding](init-gen-time.md)
- [The init generator at the stack cap](init-gen-cap-h.md)
