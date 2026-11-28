# Counting-regularity is undecidable for real-time one-counter one-reversal machines

It is undecidable whether a given real-time nondeterministic one-counter machine whose counter makes at most one reversal accepts a counting-regular language, and equally whether its complement is counting-regular.

**Theorem.** It is undecidable, given a real-time machine $M$ in $\mathrm{NCM}(1, 1)$ (a [one-way nondeterministic one-counter machine](reversal-bounded-counter-machines.md) whose counter makes at most one reversal and which reads one input symbol at every move), whether $\overline{L(M)}$ is [counting-regular](counting-regular-and-slender-languages.md). It is also undecidable, given such an $M$, whether $L(M)$ is counting-regular.

The machine built in the proof is $1$-reversal-bounded but not finitely ambiguous; the source proves the same undecidability for one-way $2$-ambiguous nondeterministic one-counter machines without a reversal bound (Theorem 30).

## Depends on

- [Reversal-bounded counter machines](reversal-bounded-counter-machines.md)
- [Counting-regular languages](counting-regular-and-slender-languages.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

As in the pushdown case, the halting problem for a deterministic Turing machine $Z$ on a blank tape is reduced, now with all configurations padded to equal length, so that halting computations are written as $w = ID_1 \# ID_3 \# \cdots \# ID_{2k-1} \diamond ID_{2k}^R \# \cdots \# ID_2^R$ with a separator $\diamond$. Inputs are expected to have the shape $x w 1^n$ with $x \in (a+b)^+$. A real-time $\mathrm{NCM}(1, 1)$ machine $M_1$ guesses one of several errors and accepts if it finds it: the input does not have this shape; $|x|_a \ne n$; $w$ does not have the shape of a computation; the configurations do not all have the same length, or the first is not initial, or the last is not halting; or some odd-numbered step $ID_i \Rightarrow ID_{i+1}$ is wrong. Each check needs at most one counter reversal, the equal lengths of the configurations being what makes the last one possible. A machine $M_2$ does the same with $|x|_b$ and the even-numbered steps, and $M$ accepts $L(M_1) \cup L(M_2)$. If $Z$ does not halt, $\overline{L(M)} = \emptyset$; if it halts with computation $w$, $\overline{L(M)} = \{x w 1^n : |x|_a = |x|_b = n\}$, which is not counting-regular. So $\overline{L(M)}$, and by the generating-function argument also $L(M)$, is counting-regular if and only if $Z$ does not halt.

## Sources

- O. H. Ibarra, I. McQuillan and B. Ravikumar, "On counting functions and slenderness of languages", *Theoretical Computer Science* 777:356–378, 2019, doi:[10.1016/j.tcs.2018.11.021](https://doi.org/10.1016/j.tcs.2018.11.021); numbering of arXiv:1903.03504v1: Theorem 29 with its proof and Theorem 30, in Section 6.
