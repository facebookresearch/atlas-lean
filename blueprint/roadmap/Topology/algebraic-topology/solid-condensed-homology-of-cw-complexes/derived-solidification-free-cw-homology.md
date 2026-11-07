# Derived solidification computes singular homology

Let $X$ be a topological space
equipped with a CW complex structure, let $n$ be a natural number, and let $\mathbb{Z}[X]$ be the
free light condensed abelian group on $X$, viewed as a complex concentrated in degree $0$ in the
derived category of light condensed abelian groups. Apply derived solidification to
$\mathbb{Z}[X]$, take the homology in cohomological degree $-n$, which is a light solid abelian
group, and regard it as a light condensed abelian group. This is an isomorphism between the
resulting light condensed abelian group and the $n$-th singular homology group $H_n(X; \mathbb{Z})$
of $X$ with integer coefficients, regarded as a discrete light condensed abelian group.

The derived category is cohomologically indexed, so the $n$-th homology group sits in degree $-n$.

## Sources

- https://github.com/dagurtomas/LeanCondensed; D. Clausen and P. Scholze, lectures on analytic stacks and light condensed mathematics.; P. Scholze, Lectures on Condensed Mathematics, https://arxiv.org/pdf/2605.03658. Problem `derived_solidification_free_CW_homology` of the lean-eval benchmark.
