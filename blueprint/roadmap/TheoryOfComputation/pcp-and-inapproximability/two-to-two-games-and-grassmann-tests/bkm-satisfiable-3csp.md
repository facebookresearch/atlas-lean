# Bhangale–Khot–Minzer: satisfiable 3-CSPs and the role of linear structure

Let $P \subseteq \Sigma^3$ be a predicate over a finite alphabet that does not support a linear embedding into a finite abelian group (formally: there is no non-trivial homomorphism-respecting embedding of the support of a distribution on $P$ into an abelian group). Then for every distribution $\mu$ on $P$ with full support on $P$ and pairwise connected marginals, every triple of $1$-bounded functions $f, g, h : \Sigma^n \to \mathbb{C}$ satisfies

$$
\Bigl| \mathbb{E}_{(x,y,z) \sim \mu^{\otimes n}} f(x)g(y)h(z) \Bigr| \le \varepsilon \quad \text{unless } f, g, h \text{ have a common low-degree correlation},
$$

and consequently, for such predicates, a dictatorship test with perfect completeness yields NP-hardness of distinguishing satisfiable instances of $\mathrm{Max}\text{-}P$ from instances of value at most $s(P) + \varepsilon$ for an explicit $s(P) < 1$.

## Proof sketch

The analytic core is an inverse theorem for the trilinear form under a non-product distribution with no abelian embedding: by a sequence of path tricks and a reduction to a CSP over an abelian group in the presence of embeddings, low-degree correlation is forced; otherwise the form is small. Combined with the standard dictatorship-test-to-PCP composition this gives hardness with perfect completeness.

## Depends on

- [d-to-d games and 2-to-2 constraints](d-to-d-games.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Proof depends on

- [d-to-d games and 2-to-2 constraints](d-to-d-games.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Sources

- A. Bhangale, S. Khot, D. Minzer, "On approximability of satisfiable k-CSPs: I", STOC (2022), arXiv:2112.04440.
