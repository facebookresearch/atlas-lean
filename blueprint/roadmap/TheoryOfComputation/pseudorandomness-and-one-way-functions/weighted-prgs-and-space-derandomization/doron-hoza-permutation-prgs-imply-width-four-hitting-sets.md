# Doron–Hoza: better PRGs for width-6 permutation ROBPs would give hitting sets for width-4 ROBPs

Let $c\in[1,2)$ be a constant. If there are explicit PRGs for width-$6$, length-$n$ standard-order permutation ROBPs with error $1/n$ and seed length $\widetilde{O}(\log^c n)$, then there are explicit hitting set generators for width-$4$, length-$n$ ROBPs with threshold $1/\mathrm{polylog}(n)$ and seed length $\widetilde{O}(\log^c n)$. The reduction has two parts:

1. explicit low-error PRGs for width-$6$ permutation ROBPs with seed $\widetilde{O}(\log^c n)$ imply explicit low-error PRGs for width-$3$ ROBPs with seed $\widetilde{O}(\log^c n)$;
2. for all $w,n,s,\varepsilon$, an explicit PRG for width-$w$ ROBPs with error $0.01/n$ and seed length $s$ implies an explicit $\varepsilon$-HSG for width-$(w+1)$ ROBPs with seed length $O(s+\log n\cdot\log(1/\varepsilon))$.

For context, when the reduction was published no explicit PRGs, WPRGs or HSGs with seed $o(\log^2 n)$ were known for width-$4$ ROBPs, whereas WPRGs with seed $\widetilde{O}(\log^{3/2}n)$ and error $1/n$ exist for polynomial-width permutation ROBPs.

## Proof sketch

The main theorem is the composition of the two parts: part 1 converts the hypothesized width-$6$ permutation PRGs into low-error PRGs for width-$3$ programs with the same seed length up to polylogarithmic factors, and part 2 with $w=3$ converts those into hitting set generators for width-$4$ programs with threshold $\varepsilon=1/\mathrm{polylog}(n)$, whose additive cost $O(\log n\cdot\log(1/\varepsilon))=\widetilde{O}(\log n)$ is absorbed in $\widetilde{O}(\log^c n)$. Each part is a black-box reduction that uses the given generator only on programs derived from the target program.

## Depends on

- [Regular and permutation ROBPs with one accept vertex, and hitting set generators](regular-permutation-robps-and-hitting-set-generators.md)

## Proof depends on

- [Pyne–Vadhan: weighted PRGs for unbounded-width permutation ROBPs with seed Õ(log^{3/2} n), impossible for PRGs](pyne-vadhan-pseudodistributions-beat-prgs.md)

## Sources

- Dean Doron and William M. Hoza, "Implications of Better PRGs for Permutation Branching Programs", APPROX/RANDOM (2025), LIPIcs 353, 28:1-28:20.
