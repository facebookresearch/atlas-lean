# Counting-regularity is undecidable for real-time 2-ambiguous one-reversal pushdown automata

It is undecidable whether a given real-time pushdown automaton with at most two accepting computations per word and at most one stack reversal accepts a counting-regular language, and equally whether its complement is counting-regular.

**Theorem.** It is undecidable, given a [pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md) $M$ that is real-time (it reads one input symbol at every move), $2$-ambiguous (every word has at most two accepting computations) and $1$-reversal-bounded (in every computation the stack height changes at most once from non-decreasing to non-increasing), whether $\overline{L(M)}$ is [counting-regular](counting-regular-and-slender-languages.md). It is also undecidable, given such an $M$, whether $L(M)$ is counting-regular.

The bound on ambiguity cannot be lowered to one: languages of unambiguous reversal-bounded pushdown automata are always strongly counting-regular. The source also shows that it is undecidable, given two real-time $1$-reversal-bounded deterministic pushdown automata accepting strongly counting-regular languages, whether the intersection of their languages is counting-regular (Theorem 27).

## Depends on

- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)
- [Counting-regular languages](counting-regular-and-slender-languages.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Let $Z$ be a single-tape deterministic Turing machine started on a blank tape. Two real-time $1$-reversal-bounded deterministic pushdown automata check alternate steps of a halting computation written, with a separator $\diamond$, as $ID_1 \# ID_3 \# \cdots \# ID_{2k-1} \diamond ID_{2k}^R \# \cdots \# ID_2^R$, so the intersection of their languages is empty or the single halting computation $w$ of $Z$. Prefixing $x \in (a+b)^+$ and appending $1^n$, with $n = |x|_a$ in the first language and $n = |x|_b$ in the second, gives deterministic languages $L_1, L_2$ whose intersection is empty if $Z$ does not halt, and otherwise $\{x w 1^n : |x|_a = |x|_b = n\}$, whose generating function $z^{|w|} \sum_n \binom{2n}{n} z^{3n}$ is not rational. The complements of $L_1$ and $L_2$ are again real-time $1$-reversal-bounded deterministic pushdown languages, and their union is accepted by a real-time $1$-reversal-bounded $2$-ambiguous pushdown automaton $M$. Then $\overline{L(M)} = L_1 \cap L_2$ is counting-regular if and only if $Z$ does not halt, and the same holds for $L(M)$, whose generating function is $1/(1 - sz)$ minus that of $L_1 \cap L_2$ for an alphabet of size $s$.

## Sources

- O. H. Ibarra, I. McQuillan and B. Ravikumar, "On counting functions and slenderness of languages", *Theoretical Computer Science* 777:356–378, 2019, doi:[10.1016/j.tcs.2018.11.021](https://doi.org/10.1016/j.tcs.2018.11.021); numbering of arXiv:1903.03504v1: Theorem 28 with its proof, which uses the languages of the proof of Theorem 27, in Section 6.
