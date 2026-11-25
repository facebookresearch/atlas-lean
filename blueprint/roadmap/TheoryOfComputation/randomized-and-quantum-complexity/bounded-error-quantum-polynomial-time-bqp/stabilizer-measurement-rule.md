# Stabilizer measurement rule

Let $\lvert \psi \rangle$ be a normalized $n$-qubit state stabilized by $n$ independent, pairwise commuting
Hermitian Pauli operators $P^{(1)}, \dots, P^{(n)}$ (a maximal set of generators, so that $\lvert \psi \rangle$ is determined
up to a global phase), and measure a Hermitian Pauli operator $M$
(outcomes $\pm 1$, projectors $(I \pm M)/2$).

1. If $M$ commutes with every $P^{(j)}$, then $M$ or $-M$ is a product of some of the $P^{(j)}$, the
   outcome is deterministic ($+1$ if $M$ is in the stabilizer group, $-1$ if $-M$ is), and the state
   and its stabilizer description are unchanged.
2. Otherwise choose a pivot $P^{(1)}$ that anticommutes with $M$ and replace every other $P^{(j)}$ that
   anticommutes with $M$ by $P^{(1)} P^{(j)}$; this leaves the stabilizer group unchanged and makes the
   pivot the only generator that anticommutes with $M$. Then both outcomes have probability $1/2$, and
   after outcome $m$ the post-measurement state is stabilized by $mM$ and the other (updated)
   generators, which give $n$ independent pairwise commuting stabilizers.

The multiplication step is required: for generators $Z_1, Z_2$ and $M = X_1 X_2$, replacing only $Z_1$
by $\pm X_1 X_2$ leaves the anticommuting pair $X_1 X_2, Z_2$; the correct second generator is $Z_1 Z_2$.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and
links it under the dependency sections.

- Statement prerequisite: measurements (POVMs and projective measurements) and the Born rule.

## Depends on

- [Pauli group, Clifford group and stabilizer states](pauli-group-clifford-group-and-stabilizer-states.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 20.3, "Updating the
  stabilizer representation after a measurement" (Cases 1 and 2).
  <https://arxiv.org/abs/1907.09415v6>
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, Caltech, 1997;
  arXiv:quant-ph/9705052. <https://arxiv.org/abs/quant-ph/9705052> Background reference.
