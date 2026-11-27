# MKtP is in E and in EXP

$\mathrm{MKtP} \in \mathrm{E}$ (deterministic time $2^{O(n)}$), and hence in EXP; for every polynomial-time computable threshold $s$, $\mathrm{MKtP}[s] \in \mathrm{EXP}$. Moreover $Kt(x) \le k$ iff some program $p$ with $|p| \le k$ outputs $x$ within $2^{k - |p|}$ steps, so a bounded exhaustive search decides it.

## Proof sketch

Enumerate all programs $p$ of length at most $s$ and run each for $2^{s - |p|}$ steps; the total work is $\sum_{\ell \le s} 2^\ell 2^{s - \ell}\,\mathrm{poly} = 2^{O(s)}$, and $s = O(|x|)$ suffices.

## Depends on

- [The minimum Kt problem MKtP](the-minimum-kt-problem.md)
- [The class E](../../complexity-classes/time-and-space-complexity-classes/e.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)

## Sources

- Y. Liu and R. Pass, "On the Possibility of Basing Cryptography on EXP ≠ BPP", CRYPTO 2021.
- E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek and D. Ronneburger, "Power from Random Strings", SIAM Journal on Computing 35(6), 2006.
