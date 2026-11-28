# Chain-free string constraints are decidable

Satisfiability of chain-free string constraints, combining transducer relations, word equations, regular memberships and linear length constraints, is decidable, and so is that of weakly chaining ones; for a fixed relation-concatenation skeleton with a chain, satisfiability over all choices of relations and side constraints is undecidable.

Use the string formulas, splitting graphs and chains of [chain-free string constraints](chain-free-string-constraints.md).

1. Every weakly chaining formula can be transformed into an equisatisfiable chain-free formula.
2. Satisfiability of chain-free formulas is decidable; hence satisfiability of weakly chaining formulas is decidable.
3. For a conjunctive formula, its *skeleton* is what remains after deleting its membership and length constraints and forgetting which relation each relational constraint uses: the ordered list of pairs of terms $(t, t')$ of its relational constraints, with their variable occurrences. Whether a formula has a chain depends only on its skeleton. For every skeleton with a chain, satisfiability is undecidable for the class of formulas with that skeleton, in which the transducers and the membership and length constraints vary freely and the alphabet may be extended by a fresh delimiter letter.

So, among classes given by a skeleton, exactly the chain-free ones are decidable. This is a statement about classes, not about single formulas: a particular formula with a chain may well be decidable on its own.

## Depends on

- [Chain-free string constraints](chain-free-string-constraints.md)

## Proof depends on

- [Acyclic transducer constraints are PSPACE-complete](acyclic-transducer-constraints-are-pspace-complete.md)
- [Cooper's theorem](../presburger-arithmetic-and-real-addition/cooper-s-theorem.md)
- [Diagonal transducer constraints are undecidable](diagonal-transducer-constraints-are-undecidable.md)

## Expansion

This node still needs its proof broken down; the source proof has these parts.

Part 1 (Theorem 1, Section 5) removes benign chains one at a time, by induction on the number of constraints labelling benign chains: along a benign chain all relations are left-sided and length-preserving, so the chain's constraints are combined, by products of length-preserving multi-tape automata and projection to the relevant tracks (with off-chain parts of the terms kept as separate tracks, possibly empty), into one equivalent constraint without that chain.

Part 2 (Theorem 2, Sections 6–7, Lemmas 3–8; Section 8). Negations are first normalized as in the definition page (with the unequal-length disjuncts for negated length-preserving relations). A splitting algorithm then works on each clause. A *left split* of $R(x \circ t, y \circ t')$ decomposes the transducer along an intermediate state and substitutes $x = x_1 x_2$ elsewhere, removing one concatenation here and possibly creating others where $x$ occurs. Splitting preserves satisfiability and chain-freeness (Lemma 3); a first phase driven by the roots of the splitting graph and a second phase in any order both terminate on chain-free clauses (Lemmas 4–8), giving an equisatisfiable chain-free and concatenation-free formula. Its transducer constraints share at most one variable pairwise, so they are synchronized into one multi-tape automaton, as for acyclic transducer constraints. Length constraints are added by computing, effectively, the Parikh image of that automaton as an existential Presburger formula over the letter counts of each track, relating it to the lengths, and deciding the conjunction with the length constraints in Presburger arithmetic.

Part 3 (Lemma 1 and its proof, Section 4 of the extended report): from a minimal chaining subset of the constraints of the skeleton, an instance $T(x, x)$ is encoded with the same skeleton by delimiting the variables along the chain with a fresh letter, forcing all other variables to be empty, using $T$ for one relation of the chain and the identity for the others, and $\Sigma^* \times \Sigma^*$ for the remaining relations. The conference version states the lemma for "every given skeleton class", while the sentence after it and the extended report make clear it concerns chaining skeleton classes; the extended report contains the proof.

## Sources

- P. A. Abdulla, M. F. Atig, B. P. Diep, L. Holík and P. Janků, "Chain-free string constraints", Automated Technology for Verification and Analysis (ATVA 2019), Lecture Notes in Computer Science 11781, Springer, 2019, pp. 277–293, doi:[10.1007/978-3-030-31784-3_16](https://doi.org/10.1007/978-3-030-31784-3_16): Sections 4–7 of the conference version; extended technical report arXiv:2307.03970v1 (author list there run together as "Mohamed Faouzi Atig Bui Phi Diep"), <https://arxiv.org/abs/2307.03970v1>: Section 4 (skeleton classes, Lemma 1 and its proof), Section 5 (Theorem 1 and its proof), Sections 6–7 (the splitting algorithm, Theorem 2, Lemmas 3–8), and Section 8 (transducer and length constraints for chain-free, concatenation-free formulas).
