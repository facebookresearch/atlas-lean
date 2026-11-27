# Rule 110 is computationally universal

The [elementary cellular automaton](elementary-cellular-automata-and-wolfram-numbers.md) rule 110 can emulate every cyclic tag
system: from a cyclic tag system and its initial tape one effectively obtains a configuration of rule 110 consisting of a
finite region flanked on the left and on the right by fixed periodic patterns, whose evolution encodes the run of the tag
system. Since cyclic tag systems emulate tag systems and these emulate Turing machines, rule 110 is computationally
universal, and, given the fixed periodic patterns to the left and right, it is undecidable whether a given finite initial
region leads to eventually periodic behavior.

A *cyclic tag system* is given by a finite cyclic list of appendants, words over $\{Y, N\}$, and acts on a finite tape over
$\{Y, N\}$: at each step it deletes the first letter of the tape and, if that letter was $Y$, appends the current appendant;
then it moves on to the next appendant in the list.

## Depends on

- [Elementary cellular automata and Wolfram numbers](elementary-cellular-automata-and-wolfram-numbers.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

This page becomes ready once:

- Tag systems emulate Turing machines, and cyclic tag systems emulate tag systems (proof prerequisites; not yet stated)
- Glider systems and the emulation of cyclic tag systems by gliders of rule 110 (proof prerequisite; not yet stated)

## Sources

- M. Cook, "Universality in elementary cellular automata", *Complex Systems* 15(1):1–40, 2004: Section 1 (rule 110), Sections 2.1–2.3 (tag systems, cyclic tag systems and glider systems), Section 4 (the construction, with periodic patterns to the left and right) and Section 4.6 (undecidable questions).
- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Theorem 2 (Cook and Wolfram).
