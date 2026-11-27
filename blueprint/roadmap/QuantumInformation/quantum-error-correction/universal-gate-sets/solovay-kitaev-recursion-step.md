# The Solovay–Kitaev recursion step

Let $\mathcal{G}$ be an [instruction set](instruction-set.md) for $SU(d)$. There is a constant $c > 0$, depending on $d$,
and a threshold $\varepsilon_2 > 0$ such that the following holds for every $\varepsilon' \le \varepsilon_2$. Suppose
every $U \in SU(d)$ has an $\varepsilon'$-approximation by a product of at most $l$ elements of $\mathcal{G}$. Then every $U \in SU(d)$ has an $\varepsilon$-approximation with $\varepsilon = c\, \varepsilon'^{3/2}$ by a
product of at most $5l$ elements of $\mathcal{G}$: approximate $U$ by $U'$, decompose $\Delta = U U'^{*}$, which is within
$\varepsilon'$ of $I$, as an approximate balanced group commutator $V W V^{*} W^{*}$, approximate $V$ and $W$ by products
$\tilde V$ and $\tilde W$ (with $\tilde V^{*}$, $\tilde W^{*}$ obtained by reversing and inverting, using that
$\mathcal{G}$ is closed under inverses), and return $\tilde V \tilde W \tilde V^{*} \tilde W^{*} U'$. Iterating from an
$\varepsilon_0$-net with $\varepsilon_0 < 1/c^2$ gives $\varepsilon_n = c^{-2} (c^2 \varepsilon_0)^{(3/2)^n}$ with
$l_n = 5^n l_0$, hence length $O(\log^{\ln 5/\ln(3/2)}(1/\varepsilon))$ for accuracy $\varepsilon$.

## Depends on

- [Instruction set for $SU(d)$](instruction-set.md)

## Proof depends on

- [Finite nets from an instruction set](epsilon-nets-from-an-instruction-set.md)
- [Balanced group commutator decomposition near the identity](../../quantum-operations/solovay-kitaev-gate-compilation/balanced-group-commutator-decomposition.md)
- [Approximate balanced group commutators in $SU(d)$](approximate-balanced-group-commutators-in-sud.md)
- [Approximating a group commutator](approximating-a-group-commutator.md)

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 3 (the pseudocode, the recurrences (1)–(3) $\epsilon_n = c_{approx} \epsilon_{n-1}^{3/2}$, $l_n = 5 l_{n-1}$, and their solution (4)–(8)) and Section 5.1, equations (21)–(22) for qudits.
