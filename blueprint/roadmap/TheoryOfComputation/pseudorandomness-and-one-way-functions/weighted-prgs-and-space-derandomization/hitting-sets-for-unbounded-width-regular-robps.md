# Bogdanov–Hoza–Prakriya–Pyne: hitting sets with seed Õ(log n · log(1/ε)) for unbounded-width regular ROBPs

There is an explicit $\varepsilon$-hitting set generator for standard-order **regular** ROBPs of length $n$, unbounded width and a single accept vertex, with seed length

$$
\widetilde{O}\bigl(\log n\cdot\log(1/\varepsilon)\bigr).
$$

For comparison Nisan's PRG has seed $O(\log n\cdot\log(wn/\varepsilon))$ and the best PRG for regular programs (Braverman–Rao–Raz–Yehudayoff) has seed $\widetilde{O}(\log(w/\varepsilon)\cdot\log n)$, both depending on the width $w$. Moreover, extending Reingold–Trevisan–Vadhan, an explicit HSG for single-accept regular ROBPs with seed length $o(\log^2 n)$ in the regime $\log w=\Theta(\log(1/\varepsilon))=\Theta(\log n)$ would imply improved HSGs for general standard-order ROBPs.

## Proof sketch

In a regular program the uniform distribution on each layer is preserved by uniformly random steps, so with a single accept vertex the probability of reaching it from a random state of an intermediate layer is controlled independently of the width. The construction exploits this width-independent structure in a recursive generator over $O(\log n)$ levels, each costing $\widetilde{O}(\log(1/\varepsilon))$ seed bits, and only needs the one-sided hitting guarantee.

## Depends on

- [Regular and permutation ROBPs with one accept vertex, and hitting set generators](regular-permutation-robps-and-hitting-set-generators.md)

## Sources

- Andrej Bogdanov, William M. Hoza, Gautam Prakriya and Edward Pyne, "Hitting Sets for Regular Branching Programs", CCC (2022), ECCC TR21-143.
