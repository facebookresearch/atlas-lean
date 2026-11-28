# Regular intersection emptiness of shuffled regular-expression equivalence is undecidable

When two regular expressions, or two words with erasable padding symbols, are given letter by letter interleaved, no algorithm decides whether a given finite automaton accepts some equivalent pair, although the sequential encoding makes the string version decidable.

**Theorem (Wolf).** Fix an alphabet $\Sigma$ with at least two letters, and let $\epsilon$ be a fresh padding symbol, not in $\Sigma$ and not the empty word. The [regular intersection emptiness problem](the-regular-intersection-emptiness-problem.md) is undecidable for:
1. *Shuffled regular-expression equivalence*: words $e_1f_1e_2f_2\cdots e_nf_n$ such that $E=e_1\cdots e_n$ and $F=f_1\cdots f_n$ are regular expressions over $\Sigma$, written as strings over $\Sigma \cup \{\emptyset,\epsilon,(,),|,*\}$, whose [denoted languages](../../regular-languages/automata-and-expressions/kleene-s-theorem/is-regex-denoted.md) satisfy $L(E)=L(F)$ (Theorem 4);
2. *Shuffled string equality with padding*: words $s_1t_1\cdots s_nt_n$ with $s_i,t_i\in\Sigma\cup\{\epsilon\}$ such that erasing the $\epsilon$ symbols from $s_1\cdots s_n$ and from $t_1\cdots t_n$ gives the same word (Corollary 2).

Section 5 of the source works over a binary alphabet; a larger alphabet changes nothing, since the reduction below uses only two letters. Items 1 and 2 are the shuffled encodings of Definitions 6 and 7. By contrast, the same problem is decidable for the unary version of item 2 and for the *sequential* encoding of Definition 9 (with $\diamond$ standing for the source's dollar-sign separator) $s_1\cdots s_n\diamond t_1\cdots t_{n'}$ of string equality (Theorems 5 and 6), so the undecidability depends on the encoding; for shuffled regular expressions over one letter, Remark 1 of the source leaves the question open.

## Depends on

- [The regular intersection emptiness problem](the-regular-intersection-emptiness-problem.md)
- [Language denoted by a regular expression](../../regular-languages/automata-and-expressions/kleene-s-theorem/is-regex-denoted.md)

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable over the binary alphabet](../../undecidable-problems/post-correspondence-problem/not-tm2-decidable-pcp-bool.md)

## Expansion

From a correspondence instance $(a_i,b_i)_{i\le n}$ the reduction builds a regular language of shuffled pairs of regular expressions that use only concatenation: the first spells $a_{i_1}\cdots a_{i_k}$ and the second $b_{i_1}\cdots b_{i_k}$ for the same index sequence. Each domino $(a_i,b_i)$ gives one block: both words are padded at their end with the padding symbol $\epsilon$, which is fresh and not in $\Sigma$, to the common length $\max(1,\lvert a_i\rvert,\lvert b_i\rvert)$, and the two are interleaved letter by letter. The lower bound $1$ makes every block nonempty: the domino $(\varepsilon,\varepsilon)$, a solution on its own, gives the block $\epsilon\epsilon$, whose halves are the one-symbol expression $\epsilon$ denoting $\{\varepsilon\}$, so it is a positive instance. The source pads only the shorter word and asserts that both halves are nonempty, which fails for this domino; the lower bound is a modification. The language is the positive closure $(\mathrm{block}_1\mid\cdots\mid\mathrm{block}_n)^+$ (proof of Theorem 4 of the source). Padding the concatenated words instead would not give a regular language: for the single domino $(a,aa)$ it would give the words $(aa)^k(\epsilon a)^k$, while the blocks give $(aa\epsilon a)^+$. Each expression denotes a single word, so a member of the language is a positive instance iff the index sequence is a solution. The expressions are already strings with padding, which gives item 2. A good expansion links pages for regular expressions written as strings over $\Sigma \cup \{\emptyset,\epsilon,(,),|,*\}$ and for the shuffled encodings of Definitions 6 to 8 and the sequential encoding of Definition 9 of the source.

## Sources

- Petra Wolf, "From decidability to undecidability by considering regular sets of instances", *Theoretical Computer Science* 899, 2022, pp. 25–38, doi:[10.1016/j.tcs.2021.11.006](https://doi.org/10.1016/j.tcs.2021.11.006); read in arXiv:1906.08027v2 ([arXiv](https://arxiv.org/abs/1906.08027v2)), whose numbering is used (separate counters for definitions, theorems and corollaries): Definitions 6–9, Theorem 4, Corollary 2, and Theorems 5 and 6.
