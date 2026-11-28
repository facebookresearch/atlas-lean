# Majority and NC1 reduce to MCSP in AC0

Majority is computed by polynomial-size non-uniform $\mathrm{AC}^0$ circuits with MCSP oracle gates, and so is all of $\mathrm{NC}^1$. Hence either $\mathrm{NEXP}\not\subseteq\mathrm{P/poly}$ or MCSP is not in $\mathrm{ACC}^0$.

**Theorem (Golovnev–Ilango–Impagliazzo–Kabanets–Kolokolova–Tal).** All circuit classes below are non-uniform. In particular $\mathrm{NC}^1$ is the class of functions computed by polynomial-size formulas, with no uniformity condition; the levels of the linked NC page are log-space uniform, so that page gives the notation only, not the class used here.

1. $\mathrm{MAJ}\in(\mathrm{AC}^0)^{\mathrm{MCSP}}$.
2. $\mathrm{NC}^1\subseteq(\mathrm{AC}^0)^{\mathrm{MCSP}}$.
3. If $\mathcal{C}\subseteq\mathrm{P/poly}$ has a complete problem under $\mathrm{TC}^0$-computable reductions that is random self-reducible via a $\mathrm{TC}^0$-computable reduction, then $\mathcal{C}\subseteq(\mathrm{AC}^0)^{\mathrm{MCSP}}$; in particular $\mathrm{GapL}\subseteq(\mathrm{AC}^0)^{\mathrm{MCSP}}$.
4. If $\mathrm{EXP}\subseteq\mathrm{P/poly}$ then $\mathrm{EXP}\subseteq(\mathrm{AC}^0)^{\mathrm{MCSP}}$; consequently, if $\mathrm{SAT}\notin(\mathrm{AC}^0)^{\mathrm{MCSP}}$ then $\mathrm{EXP}\not\subseteq\mathrm{P/poly}$.
5. Either $\mathrm{NEXP}\not\subseteq\mathrm{P/poly}$, or $\mathrm{MCSP}\notin\mathrm{ACC}^0$.

## Expansion

The proof of the $\mathrm{AC}^0[p]$ lower bound shows that MCSP with a fixed threshold solves a coin problem with bias $\varepsilon=\Theta(N^{-0.49})$. By a known reduction quoted as Theorem 2.5, any oracle that solves the $\varepsilon$-coin problem with constant advantage gives non-uniform $\mathrm{AC}^0$ circuits of size $\mathrm{poly}(n/\varepsilon)$ with oracle gates for majority on $1/\varepsilon$ bits. Combined with $\mathrm{NC}^1\subseteq(\mathrm{TC}^0)^{\mathrm{MCSP}}$ this gives item 2. For item 5, $\mathrm{NEXP}\subseteq\mathrm{P/poly}$ gives $\mathrm{NEXP}=\mathrm{EXP}$ by the easy witness lemma, so item 4 and $\mathrm{MCSP}\in\mathrm{ACC}^0$ would put NEXP in $\mathrm{ACC}^0$, contradicting Williams's theorem.


Known unstated proof prerequisites needed before this node is ready for formalization:

- Shaltiel–Viola reduction from Majority to the coin problem in AC0 (Golovnev et al. Theorem 2.5)
- Oliveira–Santhanam inclusion $\mathrm{NC}^1 \subseteq (\mathrm{TC}^0)^{\mathrm{MCSP}}$ (Golovnev et al., before Corollary 5.2)

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [AC0](../../../complexity-classes/time-and-space-complexity-classes/ac0.md)
- [ACC0](../../../complexity-classes/time-and-space-complexity-classes/acc0.md)
- [Majority](../../../complexity-classes/time-and-space-complexity-classes/majority-dec.md)
- [NC](../../../complexity-classes/time-and-space-complexity-classes/nc.md)
- [The complexity class NEXP](../../../complexity-classes/time-and-space-complexity-classes/nexp.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [MCSP is not in AC0(p)](mcsp-is-not-in-ac0-p.md)
- [Williams: NEXP is not in ACC0](../../williams-nexp-not-in-acc0.md)
- [Impagliazzo–Kabanets–Wigderson easy witness lemma for NEXP](../../algorithmic-method-nqp-and-almost-everywhere-bounds/easy-witness-ikw.md)

## Sources

- Alexander Golovnev, Rahul Ilango, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, Avishay Tal, "AC^0[p] Lower Bounds Against MCSP via the Coin Problem", *International Colloquium on Automata, Languages, and Programming (ICALP)*, 2019, https://doi.org/10.4230/LIPIcs.ICALP.2019.66 (Corollaries 5.1, 5.2, 5.4, 5.6 and 5.7, Theorems 2.5, 5.3 and 5.5).
