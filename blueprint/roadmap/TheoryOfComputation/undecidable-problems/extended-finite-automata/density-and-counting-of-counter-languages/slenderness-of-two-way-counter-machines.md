# Slenderness is undecidable for two-way deterministic machines with two reversal-bounded counters

It is undecidable, given a two-way deterministic finite automaton with two reversal-bounded counters (and, in one version, a number $k$), whether it accepts a $k$-slender language, or a slender language, even when the language is letter-bounded.

**Theorem.** Let $2\mathrm{DCM}(2)$ denote the two-way deterministic finite automata with end-markers on both sides of the input, augmented with two reversal-bounded counters (as in [reversal-bounded counter machines](reversal-bounded-counter-machines.md), but with a two-way input head).

1. It is undecidable, given $k$ and a $2\mathrm{DCM}(2)$ machine $M$, whether $L(M)$ is [$k$-slender](slender-languages.md), even when $L(M)$ is a subset of $a_1^* \cdots a_r^*$ for given letters $a_1, \dots, a_r$.
2. It is undecidable, given a $2\mathrm{DCM}(2)$ machine $M$, whether $L(M)$ is slender, even when $L(M)$ is letter-bounded.

With one counter the first problem is decidable: it is decidable, given $k$ and a $2\mathrm{DCM}(1)$ machine, whether it accepts a $k$-slender language (Theorem 35 of the source).

## Depends on

- [Reversal-bounded counter machines](reversal-bounded-counter-machines.md)
- [Slender languages](slender-languages.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

It is known (Ibarra) that emptiness is undecidable for $2\mathrm{DCM}(2)$ machines accepting subsets of $b_1^* \cdots b_r^*$ for given $b_1, \dots, b_r$. Given such a machine $M$ and new symbols $c, d$, a $2\mathrm{DCM}(2)$ machine $M'$ accepts $b_1^{i_1} \cdots b_r^{i_r} c^i d^j$ whenever $M$ accepts $b_1^{i_1} \cdots b_r^{i_r}$, for all $i, j$. If $L(M)$ is empty so is $L(M')$; otherwise $L(M')$ has unboundedly many words of large lengths. So $L(M')$ is $k$-slender, respectively slender, if and only if $L(M) = \emptyset$, which is undecidable.

## Sources

- O. H. Ibarra, I. McQuillan and B. Ravikumar, "On counting functions and slenderness of languages", *Theoretical Computer Science* 777:356–378, 2019, doi:[10.1016/j.tcs.2018.11.021](https://doi.org/10.1016/j.tcs.2018.11.021); numbering of arXiv:1903.03504v1: the definition of $2\mathrm{DCM}(k)$ in Section 7, Theorem 36 with its proof, and Theorem 35.
