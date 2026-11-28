# The 2-to-2 Games Theorem (imperfect completeness)

For every $\varepsilon > 0$ there is $R = R(\varepsilon)$ such that, given a $2$-to-$2$ label-cover game with label set $[2R]$, it is NP-hard to distinguish between

- **(YES)** the value is at least $1 - \varepsilon$, and
- **(NO)** the value is at most $\varepsilon$.

## Proof sketch

Start from a label-cover instance with small soundness given by the PCP theorem with parallel repetition, whose labels are linear functions on large subspaces. Replace each label by its Grassmann encoding and compose with the Grassmann test, obtaining $2$-to-$2$ constraints; the outer constraints are embedded by restricting to subspaces with a random side condition, which costs completeness $1 - \varepsilon$. Soundness decodes a strategy of value $\varepsilon$ via the zoom-local structure lemma into list-decoded linear functions on zooms, which yield a good labeling of the outer instance; the zoom-local lemma rests on the near-perfect expansion of pseudorandom sets in the Grassmann graph.

## Depends on

- [d-to-d games and 2-to-2 constraints](d-to-d-games.md)

## Proof depends on

- [Zoom-local soundness structure of the Grassmann test](grassmann-test-completeness-local.md)
- [Equivalence of Grassmann, shortcode and bilinear small-set expansion](shortcode-equivalence.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Sources

- S. Khot, D. Minzer, M. Safra, "On independent sets, 2-to-2 games, and Grassmann graphs", STOC (2017), ECCC TR16-124.
- I. Dinur, S. Khot, G. Kindler, D. Minzer, M. Safra, "Towards a proof of the 2-to-1 games conjecture?", STOC (2018), ECCC TR16-198.
- I. Dinur, S. Khot, G. Kindler, D. Minzer, M. Safra, "On non-optimally expanding sets in Grassmann graphs", STOC (2018); Israel Journal of Mathematics 243 (2021), ECCC TR17-094.
- S. Khot, D. Minzer, M. Safra, "Pseudorandom sets in Grassmann graph have near-perfect expansion", FOCS (2018); Annals of Mathematics 198 (2023), ECCC TR18-006.
- B. Barak, P. Kothari, D. Steurer, "Small-set expansion in shortcode graph and the 2-to-2 conjecture", ITCS (2019), arXiv:1804.08662.
- S. Khot, D. Minzer, D. Moshkovitz, M. Safra, "Small set expansion in the Johnson graph", ECCC TR18-078 (2018).
