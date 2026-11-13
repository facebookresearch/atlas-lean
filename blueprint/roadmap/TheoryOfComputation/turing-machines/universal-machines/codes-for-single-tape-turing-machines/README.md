# Codes for single-tape Turing machines

## Halting within a number of steps

- [Bounded halting of a single-tape machine](halts-within.md)
- [Halting within a bound is monotone in the bound](mono.md)
- [Halting is halting within some number of steps](dom-eval-iff-exists-halts-within.md)

## Codes

- [Codes for single-tape machines](code.md)
- [Decoding an action](decode-stmt.md)
- [Symbol of an input bit](bit-sym.md)
- [Input word of a list of bits](input.md)
- [Single-tape codes as tables](equiv-table.md)
- [Table lookup of a code](lookup.md)
- [The machine of a single-tape code](machine.md)
- [States of a single-tape code](states.md)
- [Codes denote finite machines](supports-machine.md)

## Explicit configurations

- [Explicit configurations](cfg.md)
- [Configurations as tuples](equiv-prod.md)
- [TM0 configuration of a simulation configuration](to-tm0.md)
- [Acting on a configuration](act.md)
- [Output of a configuration](output.md)
- [Initial configuration of the code simulation](init.md)
- [One step of a code](step.md)
- [One step of a code, or stay when halted](step-or-stay.md)
- [Clocked configuration of a code](cfg-after.md)
- [The clocked evaluator](eval-steps.md)

## Agreement with Mathlib's semantics

- [Explicit steps agree with the decoded machine](step-to-tm0.md)
- [The explicit initial configuration is the machine's](init-to-tm0.md)
- [The output of a configuration as a Mathlib half-tape](right-to-tm0.md)
- [Iterated steps of the decoded machine](iterate-step-to-tm0.md)
- [Bounded halting of a decoded machine through its simulation](halts-within-machine-iff.md)
- [Definedness of the clocked evaluator](is-some-eval-steps-iff-step-eq-none.md)
- [Clocked halting](is-some-eval-steps-iff.md)
- [Characterization of clocked results](eval-steps-eq-some-iff-output.md)
- [Monotonicity of the single-tape clocked evaluator](eval-steps-mono.md)
- [Clocked results agree with the machine's semantics](eval-eq-some-of-eval-steps-eq-some.md)
- [Unclocked halting](dom-eval-iff-exists-is-some-eval-steps.md)

## Every finite machine has a code

- [Universality of codes](exists-code.md)

## Primitive recursiveness

- [The clocked evaluator is primitive recursive](primrec-eval-steps.md)
