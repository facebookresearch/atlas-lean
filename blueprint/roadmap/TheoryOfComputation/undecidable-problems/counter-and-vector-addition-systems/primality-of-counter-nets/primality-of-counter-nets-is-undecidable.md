# Primality and dimension-minimality of counter nets are undecidable

No algorithm decides whether a two-dimensional counter net is prime, that is, whether its language is not an intersection of one-counter-net languages, nor whether some one-counter net accepts the same language.

**Theorem.** The following problems are undecidable, already for $2$-dimensional [counter nets](counter-nets.md):

1. (*primality*) given a $k$-CN $\mathcal A$, is $\mathcal A$ [prime](prime-and-dimension-minimal-counter-nets.md)?
2. (*dimension-minimality*) given a $k$-CN $\mathcal A$, is $\mathcal A$ dimension-minimal?

(Theorem 2 of the source.)

For $1$-dimensional counter nets both problems are undecidable for a simpler reason: there, compositeness and dimension-minimality ask whether the language is regular, which is undecidable for one-counter nets. The point of the theorem is that undecidability persists when the lower dimension is not the degenerate dimension $0$. In contrast, regularity of deterministic $k$-CNs is decidable (from the same source).

## Depends on

- [Counter nets](counter-nets.md)
- [Prime and dimension-minimal counter nets](prime-and-dimension-minimal-counter-nets.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Trace inclusion and trace equivalence of one-counter nets are undecidable](../trace-equivalence-of-one-counter-nets/trace-inclusion-of-one-counter-nets-is-undecidable.md)

## Expansion

The proof reduces from non-containment of one-counter nets, undecidable by Hofman, Mayr and Totzke (P. Hofman, R. Mayr and P. Totzke, "Decidability of weak simulation on one-counter nets", *28th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2013)*, IEEE, 2013, pp. 203–212, as cited in the source; the trace-inclusion case, in which every state accepts and both counters start at $0$, already suffices): given $1$-CNs $\mathcal A$ and $\mathcal B$, is $L(\mathcal A)\not\subseteq L(\mathcal B)$? Its key ingredient is an explicit $2$-CN $\mathcal P$ that is prime (the source's main technical theorem, proved by new pumping arguments for nondeterministic two-counter nets). From $\mathcal A$, $\mathcal B$ and $\mathcal P$ one builds, with a fresh separator letter $\#$, a $2$-CN $\mathcal C$ accepting $u\#v$ when $u\in L(\mathcal A)$ and $\mathcal P$ accepts $v$ starting from the maximal counter value with which an accepting run of $\mathcal A$ ends on $u$, or when $u\in L(\mathcal B)$ and $v$ is any word over the alphabet of $\mathcal P$. If $L(\mathcal A)\subseteq L(\mathcal B)$, the first branch is redundant and $\mathcal C$ is equivalent to a $1$-CN, so $\mathcal C$ is neither dimension-minimal nor prime. Otherwise a word $u\in L(\mathcal A)\setminus L(\mathcal B)$ fixes the branch, and the primality argument for $\mathcal P$ adapts to show that $\mathcal C$ is prime, hence dimension-minimal.

## Sources

- Shaull Almagor, Guy Avni, Henry Sinclair-Banks and Asaf Yeshurun, "Dimension-Minimality and Primality of Counter Nets", in *Foundations of Software Science and Computation Structures (FoSSaCS 2024)*, Lecture Notes in Computer Science, Springer, 2024, pp. 229–249, doi:[10.1007/978-3-031-57231-9_11](https://doi.org/10.1007/978-3-031-57231-9_11); read in arXiv:2307.14492v2 ([arXiv](https://arxiv.org/abs/2307.14492v2)), whose numbering is used: Theorem 2 (Section 5, primality and dimension-minimality are undecidable for $2$-CNs) and its proof, Theorem 1 (Section 4, the $2$-CN $\mathcal P$ is prime), the discussion of $1$-CNs and regularity in the introduction, and Theorem 3 (end of Section 5, regularity of deterministic counter nets is decidable).
