# Universality of integer weighted automata on infinite words is undecidable

No algorithm decides whether an integer weighted automaton accepts every infinite word, where a word is accepted when some run has a prefix of total weight zero ending in a final state; the same holds under reverse acceptance.

**Theorem (Halava, Harju, Niskanen and Potapov).** For [integer weighted automata on infinite words](integer-weighted-automata-on-infinite-words.md):
1. it is undecidable whether $L(\mathcal A)=A^\omega$;
2. equivalently, it is undecidable whether some infinite word has, on every run, only prefixes of nonzero weight;
3. it is undecidable whether $L_R(\mathcal A)=A^\omega$ under reverse acceptance.

## Depends on

- [Integer weighted automata on infinite words](integer-weighted-automata-on-infinite-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from the infinite Post correspondence problem, undecidable for instances with $8$ letters (Dong and Liu, improving Halava and Harju): an infinite word $w$ is a solution of $(g,h)$ if for every proper prefix $p$ of $w$, one of $g(p)$, $h(p)$ is a proper prefix of the other. The automaton reads a candidate infinite word and nondeterministically guesses a position where $g$ and $h$ disagree, using the weight as a counter to compare positions in the two images; a zero-weight prefix in a final state certifies a mismatch. Hence $L(\mathcal A)=A^\omega$ iff the instance has no infinite solution. Reversing all transitions and swapping initial and final states gives item 3.

## Sources

- Vesa Halava, Tero Harju, Reino Niskanen and Igor Potapov, "Weighted automata on infinite words in the context of Attacker–Defender games", *Information and Computation* 255, 2017, pp. 27–44, doi:[10.1016/j.ic.2017.05.001](https://doi.org/10.1016/j.ic.2017.05.001); read in arXiv:1411.4796v3 ([arXiv](https://arxiv.org/abs/1411.4796v3)), whose numbering is used: Section 3: Lemma 1 (solutions and the language), Theorem 2 (universality), Corollary 3 and Theorem 4 (reverse acceptance); Section 2 for the infinite Post correspondence problem.
