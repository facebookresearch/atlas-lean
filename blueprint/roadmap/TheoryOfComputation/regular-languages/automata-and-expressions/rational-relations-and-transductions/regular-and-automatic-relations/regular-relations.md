# Regular relations

A relation between words is *regular*, or synchronized rational, if a finite automaton reading the words letter by letter in
parallel, after padding the shorter ones with a blank, accepts exactly its tuples.

Let $\Sigma$ be a finite alphabet, $\bot \notin \Sigma$ a padding symbol and $\Sigma_\bot = \Sigma \cup \{\bot\}$. For words
$w_1, \dots, w_n \in \Sigma^*$ let $\ell = \max_i |w_i|$; their *convolution* $w_1 \otimes \cdots \otimes w_n$ is the word of
length $\ell$ over $\Sigma_\bot^n$ whose $k$-th letter is $(a_1, \dots, a_n)$, where $a_i$ is the $k$-th letter of $w_i$ if
$|w_i| \ge k$ and $a_i = \bot$ otherwise. A relation $R \subseteq (\Sigma^*)^n$ is a *regular $n$-ary relation* if some finite
automaton over the alphabet $\Sigma_\bot^n$ accepts exactly the language
$\{w_1 \otimes \cdots \otimes w_n : (w_1, \dots, w_n) \in R\}$. The class of regular $n$-ary relations is written
$\mathrm{REG}_n$.

Every recognizable relation, a finite union of products $L_1 \times \cdots \times L_n$ of regular languages, is regular, and
every regular relation is [rational](../rational-relations-and-transducers.md). The prefix relation and equality of words are
regular, and the suffix relation is rational but not regular; the subword (factor) relation and the subsequence relation are
rational. Both inclusions are strict for $n \ge 2$. Recognizable and regular relations are closed under intersection, rational
relations are not.

## Depends on

- [Rational relations and transducers](../rational-relations-and-transducers.md)

## Proof depends on

None.

## Sources

- P. Barceló, D. Figueira and L. Libkin, "Graph logics with rational relations", *Logical Methods in Computer Science* 9(3), paper 1, 2013, doi:10.2168/LMCS-9(3:1)2013; Section 2 of the version arXiv:1304.4150v2 (convolution, regular relations, the inclusions between recognizable, regular and rational relations, and the examples prefix, suffix, subword and subsequence).
