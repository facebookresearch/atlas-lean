# Antichain growth of a language

Over an alphabet with a partial order, words are ordered lexicographically; the antichain growth of a language measures how fast the largest sets of pairwise incomparable words of each length grow.

**Definition.** Let $\Sigma$ be a finite alphabet with a partial order $\preceq$. The *lexicographic partial order* induced on $\Sigma^*$, also written $\preceq$, is given by: $\varepsilon \preceq w$ for every word $w$, and for letters $x, y \in \Sigma$ and words $w, w'$, $xw \preceq yw'$ iff either $x \prec y$, or $x = y$ and $w \preceq w'$. Words $u, v$ are *comparable*, written $u \sim v$, if $u \preceq v$ or $v \preceq u$. A language $L \subseteq \Sigma^*$ is a *chain* if any two of its words are comparable, and an *antichain* if any two distinct words of it are incomparable. For $n \in \mathbb{N}$ let $L_{=n} = \{w \in L : |w| = n\}$. A language $L$ is an *antichain family* if $L_{=n}$ is an antichain for every $n$. A language $L$ is *exponential* if $\limsup_{n \to \infty} |L_{=n}| / 2^{\epsilon n} > 0$ for some $\epsilon > 0$, and *polynomial* if $\limsup_{n \to \infty} |L_{=n}| / n^k < \infty$ for some $k$. A language $L$ has *exponential antichain growth* if it contains an exponential antichain family, and *polynomial antichain growth* if every antichain family contained in $L$ is polynomial.

With the discrete order on $\Sigma$, in which distinct letters are incomparable, antichain growth is the ordinary growth of the language. The size of the largest antichain among the words of length $n$ is the *width* of $L_{=n}$.

Antichain growth measures the information that can leak from a deterministic system modeled as a finite-state transducer, where the order on letters records which outputs an observer can distinguish. Every regular language has either polynomial or exponential antichain growth (Theorem 16 of the source, for NFAs, and Corollary 17), and which one is decidable in polynomial time for NFAs (Theorem 18); every context-free language also has polynomial or exponential antichain growth (Theorem 34).

## Depends on

- [Partially ordered set](../../../Order/ordered-sets/partial-order.md)

## Proof depends on

None.

## Sources

- D. Mestel, "Widths of Regular and Context-Free Languages", in *39th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2019)*, Leibniz International Proceedings in Informatics 150, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2019, article 49, doi:[10.4230/LIPIcs.FSTTCS.2019.49](https://doi.org/10.4230/LIPIcs.FSTTCS.2019.49); read as arXiv:1709.08696v5, whose numbering is used here: Definitions 1, 2, 7, 8 and 9, Theorem 16, Corollary 17, Theorem 18 and Theorem 34.
