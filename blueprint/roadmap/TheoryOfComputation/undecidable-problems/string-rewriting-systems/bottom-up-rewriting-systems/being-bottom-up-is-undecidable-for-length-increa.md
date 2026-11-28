# Being bottom-up is undecidable for length-increasing semi-Thue systems

For every bound $k \ge 1$, no algorithm decides whether a finite length-increasing semi-Thue system is bottom-up with bound $k$.

**Theorem (Durand and Sénizergues).** For every $k \ge 1$, it is undecidable whether a given finite length-increasing semi-Thue system is $\mathrm{BU}(k)$, in the sense of
[bottom-up semi-Thue systems](bottom-up-semi-thue-systems.md), and likewise whether it is $\mathrm{BU}^-(k)$.

The bound $k$ is fixed and the system is the input. The source shows that $\mathrm{BU}(k)$ is decidable for length-increasing semi-Thue systems with no right-linear recursion, that is, with no sequence of rules $l_1 \to r_1, \dots, l_n \to r_n$, $n \ge 2$, such that each $l_{i+1}$ is a suffix of $r_i$ and $l_1 = l_n$ (Proposition 5.7).

## Depends on

- [Bottom-up semi-Thue systems](bottom-up-semi-thue-systems.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether a context-free grammar generates every word is undecidable](../../undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-univ.md)

## Expansion

The proof reduces a modified universality problem for context-free grammars with terminals $\{z_1, z_2\}$: does $S_1 \to^* s S_1$ hold for every $s \in \{z_1, z_2\}^*$? It is
undecidable by the undecidability of universality of context-free grammars. For $k = 1$, the semi-Thue system consists of the grammar rules together with
$S_0 \to z_1 S_0$, $S_0 \to z_2 S_0$ and $S_0 a_1 \to S_1 a_1$ for fresh letters $S_0, a_1$; it is $\mathrm{BU}(1)$ exactly when the grammar instance is positive. For larger $k$, the
construction uses fresh letters $S_{0,1}, \dots, S_{0,k}$ and $a_1, \dots, a_k$.

## Sources

- I. Durand and G. Sénizergues, "Bottom-up rewriting for words and terms", *Journal of Symbolic Computation* 67:93–121, 2015, doi:10.1016/j.jsc.2014.06.001; read in arXiv:0903.2554v2: Theorem 5.11 in Section 5.2 ("Decidable/undecidable cases for semi-Thue systems"), Proposition 5.8 on $\mathrm{BU}(1)$ with Lemmas 5.9 and 5.10 before it, and Proposition 5.7 (the decidable cases) in the same section, with the numbering of that version.
