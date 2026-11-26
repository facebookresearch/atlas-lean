# Hoza: randomized space S is in deterministic space O(S^{3/2} / sqrt(log S))

Recall the Saks–Zhou theorem $\mathsf{BPSPACE}[S]\subseteq\mathsf{DSPACE}[S^{3/2}]$. As a consequence of the work on weighted PRGs, for every space-constructible $S(n)\ge\log n$, every bounded-error randomized decision algorithm running in space $S$ (and halting with probability one) can be simulated deterministically in space

$$
O\Bigl(\frac{S^{3/2}}{\sqrt{\log S}}\Bigr).
$$

This is the first improvement on Saks–Zhou in over two decades; it already follows from earlier weighted PRGs, and the seed-length improvement of Hoza is not needed for it.

## Proof sketch

In the Saks–Zhou framework one repeatedly approximates powers of the transition matrix using a generator with error $2^{-\Theta(S)}$ and rounds with a random shift; the seed length of the generator at this tiny error controls the space per recursion level. A WPRG whose seed has additive dependence $O(\log(1/\varepsilon))$ rather than Nisan's $O(\log n\cdot\log(1/\varepsilon))$ lets one choose longer segments and fewer levels, and balancing the parameters saves a $\sqrt{\log S}$ factor.

## Depends on

- [Braverman–Cohen–Garg: weighted PRGs and hitting sets with near-optimal error dependence for ROBPs](braverman-cohen-garg-near-optimal-error.md)
- [Deterministic space classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Braverman–Cohen–Garg: weighted PRGs and hitting sets with near-optimal error dependence for ROBPs](braverman-cohen-garg-near-optimal-error.md)

## Sources

- William M. Hoza, "Better Pseudodistributions and Derandomization for Space-Bounded Computation", APPROX/RANDOM (2021), ECCC TR21-048.
