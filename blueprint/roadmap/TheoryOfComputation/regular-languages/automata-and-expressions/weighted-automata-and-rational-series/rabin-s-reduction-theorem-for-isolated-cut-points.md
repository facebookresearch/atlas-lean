# Rabin's reduction theorem for isolated cut-points

Let $\mathcal{A}$ be a [probabilistic automaton](probabilistic-automata-and-cut-point-languages.md) and $\lambda$ a cut-point that is isolated for $\mathcal{A}$.
Then the cut-point language $L_{\mathcal{A}}(\lambda) = \{w : P_{\mathcal{A}}(w) \ge \lambda\}$ is regular (Rabin). Without isolation this fails: probabilistic
automata accept non-regular cut-point languages, so they are in general more powerful than deterministic finite automata.

## Depends on

- [Probabilistic automata and cut-point languages](probabilistic-automata-and-cut-point-languages.md)

## Sources

- M. O. Rabin, "Probabilistic automata", *Information and Control* 6, 1963: the abstract, describing Theorem 2 (probabilistic automata are more powerful than deterministic ones) and the reduction theorem, Theorem 3.
- H. Gimbert and Y. Oualhadj, "Probabilistic automata on finite words: decidable and undecidable problems", *Proceedings of ICALP 2010*, Lecture Notes in Computer Science 6199, Springer, 2010 (version <https://hal.science/hal-00456538v2>): Section 3, Theorem 2 (Rabin).
