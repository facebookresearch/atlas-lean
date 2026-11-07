# Cook-Levin: the precomputation, composed with the assembled generator

## [LIB] Counter-view additions: decrement, multi-target transfer, the power loop

- [Unit targets of a multi-target transfer](tg.md)
- [Counters after a multi-target transfer](xf.md)
- [Multi-target transfer](xfer-s.md)
- [Stages of the power loop](pw.md)
- [Power-loop program](pow-s.md)
- [Step budget of the power loop](pow-b.md)
- [The power loop](pow-run.md)

## Horner evaluation of a polynomial on counters

- [Stages of a Horner round](hw.md)
- [The statements of one Horner round](horn-s.md)
- [Step count of one Horner round](horn-step.md)
- [One Horner round](horn-round.md)
- [Horner value](horn-val.md)
- [Step count of the Horner rounds](horn-t.md)
- [Horner rounds](horner-run.md)
- [Splitting off the starting accumulator in Horner evaluation](horn-val-eq.md)
- [Coefficient list of a polynomial](coeffs.md)
- [Horner's rule](horn-val-coeffs.md)

## [CNT] The precomputation's counter program

- [Scratch counters of the counter program](ps.md)
- [Target counters of the counter program](pt.md)
- [Counters of the counter program](cc.md)
- [Labels of the counter program](pl.md)
- [Horner-round labels indexed by natural numbers](hlab.md)
- [The counter program](cprog.md)
- [Total length bound](m-of.md)
- [The precomputed time bound](tof.md)
- [Start counter values](f0.md)
- [Counter values after the Horner loop](f1.md)
- [Counter values before the power loop](f2.md)
- [Counter values after the power loop](f3.md)
- [Target counter values](tv.md)
- [Counter values at the end of the counter program](f4.md)
- [Step budget of the counter program](c-b.md)
- [The counter program's run](cprog-run.md)

## [FULL] The full machine: read loop, counter program, host

- [Stacks of the full machine](fk.md)
- [Alphabets of the full machine](f.md)
- [Labels of the full machine](fl.md)
- [Host counter of each target](tgt.md)
- [Stack renaming of the counter program](e-c.md)
- [Embedding of the counter program's stacks](emb-c.md)
- [Embedding of the host's stacks](emb-h.md)
- [The read loop](rd-t.md)
- [Stacks during the read loop](fst.md)
- [The read loop's run](read-run.md)

## [COMP] The full program and its run

- [The full program](fprog.md)
- [The precomputation](pre-run.md)

## [REAL] The full machine on the real generators: raw input to emitted formula

- [The full program on the real generators](full-prog.md)
- [Step bound of the full machine](full-b.md)
- [The composed machine, raw input to formula](full-run.md)
- [The full machine as a finite multi-stack Turing machine](full-tm.md)
- [Initial configuration of the full machine](init-list-full.md)

## [POLY] The step bound is a polynomial in `|s|`

- [Polynomial functions on the naturals](is-poly.md)
- [The Horner step count is polynomial](horn-t-2.md)
- [Polynomial time bound of the composed machine](full-time-poly.md)
