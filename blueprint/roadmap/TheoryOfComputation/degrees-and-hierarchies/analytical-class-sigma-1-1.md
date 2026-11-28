# The analytical class Σ¹₁ and Σ¹₁-hardness under many-one reductions

A decision problem on the natural numbers is in $\Sigma^1_1$ if it asks for the existence of an infinite binary sequence satisfying an arithmetical condition; $\Sigma^1_1$-complete problems are not arithmetical, and in particular not decidable.

**Definition.** A decision problem $P : \mathbb{N} \to \{0, 1\}$ is in $\Sigma^1_1$, the first existential level of the analytical hierarchy (one existential quantifier over $2^{\mathbb{N}}$, equivalently over functions $\mathbb{N} \to \mathbb{N}$, in front of an arithmetical matrix), if there is an arithmetical relation $R$, evaluated with an oracle $f$, such that $P(n) = 1$ exactly when there is $f \in 2^{\mathbb{N}}$ with $R^f(n)$. A problem is *$\Sigma^1_1$-hard* if every problem in $\Sigma^1_1$ many-one reduces to it, and *$\Sigma^1_1$-complete* if moreover it is in $\Sigma^1_1$.

Every arithmetical problem is in $\Sigma^1_1$, and a $\Sigma^1_1$-complete problem is not arithmetical; in particular it is undecidable.

## Depends on

None.

## Proof depends on

None.

## Sources

- A. Callard and B. Hellouin de Menibus, "The Aperiodic Domino Problem in Higher Dimension", *39th International Symposium on Theoretical Aspects of Computer Science (STACS 2022)*, Leibniz International Proceedings in Informatics 219, 2022, Article 19, doi:[10.4230/LIPIcs.STACS.2022.19](https://doi.org/10.4230/LIPIcs.STACS.2022.19); numbering of arXiv:2202.07377v1: Definition 6 (the class $\Sigma^1_1$) and the hierarchy of undecidability in Section 2.2.
