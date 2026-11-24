# Validity of first-order sentences is undecidable

There is no Turing machine that, started on a tape containing a first-order sentence $B$, halts with output $1$ if $B$ is valid and $0$ otherwise. The proof reduces the halting problem: from a machine $M$ and an input $w$ one computes a sentence, in a fixed finite language describing configurations of $M$, that is valid exactly when $M$ halts on $w$. Validity is nevertheless semi-decidable: some Turing machine halts with output $1$ exactly on the valid sentences and runs forever on the others, by enumerating all derivations and using soundness and completeness.

## Sources

- The Open Logic Project, *Sets, Logic, Computation*, Section 15.8, Theorems 15.16 and 15.18, <https://builds.openlogicproject.org/courses/sets-logic-computation/slc-screen.pdf>
- A. Church, "A note on the Entscheidungsproblem", *Journal of Symbolic Logic* 1(1):40–41, 1936
- A. M. Turing, "On computable numbers, with an application to the Entscheidungsproblem", *Proceedings of the London Mathematical Society* 42:230–265, 1937
