# Combinatorial substitutions, consistency and overlapping

A $d$-dimensional combinatorial substitution maps each cell type to a pattern and uses concatenation rules, one for each allowed pair of cells at a given offset, to fix the relative position of their images. It is consistent if the position of the images never depends on the path of rules used, and non-overlapping if images of distinct cells never overlap.

**Definition.** Fix an alphabet $\mathcal{A}$ of cell types and $d \ge 1$. A *cell* is a pair $c = [v, t]$ with $v \in \mathbb{Z}^d$ and $t \in \mathcal{A}$, and a *pattern* is a finite union of cells with distinct vectors; its *support* is $\mathrm{supp}(P) = \{v : [v, t] \in P\}$, and patterns are translated in the obvious way. A *$d$-dimensional substitution* $\sigma$ on $\mathcal{A}$ consists of

- a *base rule* $\sigma_{\mathrm{base}}$ assigning to each $t \in \mathcal{A}$ a $d$-dimensional pattern, extended to cells by $\sigma_{\mathrm{base}}([v, t]) = \sigma_{\mathrm{base}}(t)$;
- a finite set of *concatenation rules* $(t, t', u) \mapsto v$ with $t, t' \in \mathcal{A}$ and $u, v \in \mathbb{Z}^d$, meaning that two cells of types $t, t'$ separated by $u$ have images $\sigma_{\mathrm{base}}(t), \sigma_{\mathrm{base}}(t')$ separated by $v$.

Substitutions are *deterministic*: a left-hand side $(t, t', u)$ occurs in at most one rule, and then $(t', t, -u)$ occurs in none. For cells $c = [u, t]$, $c' = [u', t']$ let $\sigma_{\mathrm{rule}}(c, c') = v$ if $(t, t', u' - u) \mapsto v$ is a rule and $-v$ if $(t', t, u - u') \mapsto v$ is a rule. The *starting patterns* are the two-cell patterns $\{[0, t], [u, t']\}$ of left-hand sides, forming the set $\mathcal{C}_\sigma$. A *$\mathcal{C}_\sigma$-path* is a sequence of cells $\gamma = (c_1, \dots, c_n)$ in which each $\{c_i, c_{i+1}\}$ is a translate of a starting pattern and cells with the same vector are equal; its *image vector* is $\mathbf{w}_\sigma(\gamma) = \sum_{i=1}^{n-1} \sigma_{\mathrm{rule}}(c_i, c_{i+1})$. A pattern $P$ is *$\mathcal{C}_\sigma$-covered* if any two of its cells are joined by a $\mathcal{C}_\sigma$-path of cells of $P$.

The substitution $\sigma$ is *consistent on* a $\mathcal{C}_\sigma$-covered pattern $P$ if any two $\mathcal{C}_\sigma$-paths of $P$ with the same endpoints have the same image vector, and *non-overlapping on* $P$ if for all distinct cells $c, c'$ of $P$ and every $\mathcal{C}_\sigma$-path $\gamma$ of $P$ from $c$ to $c'$, the support of $\sigma_{\mathrm{base}}(c)$ is disjoint from the support of $\sigma_{\mathrm{base}}(c')$ translated by $\mathbf{w}_\sigma(\gamma)$. It is *consistent* (respectively *non-overlapping*) if it is so on every $\mathcal{C}_\sigma$-covered pattern. A *domino substitution* is a two-dimensional substitution whose rules all have $u \in \{\pm(1, 0), \pm(0, 1)\}$; it is *domino-to-domino* if moreover, for every rule $(t, t', u) \mapsto v$, we have $v \in \{\pm(1, 0), \pm(0, 1)\}$ and both $\sigma_{\mathrm{base}}(t)$ and $\sigma_{\mathrm{base}}(t')$ are a single cell at $(0, 0)$ (types occurring in no rule are unrestricted).

Consistency makes the relative positions of the translated images independent of the paths used; for a non-overlapping substitution these images then form a pattern, so the image of a covered pattern is well defined up to translation (Section 2.5 of the source). For a two-dimensional *domino-complete* substitution, one whose starting patterns are all possible dominoes, consistency is decidable: it holds if and only if it holds on every $2 \times 2$ pattern (Theorem 4.1). For a consistent two-dimensional domino-complete substitution, non-overlapping is decidable by checking finitely many systems of linear equations over the integers (Theorem 4.4), although overlaps can first appear on arbitrarily wide patterns (Example 4.6).

## Depends on

None.

## Proof depends on

None.

## Sources

- T. Jolivet and J. Kari, "Consistency of multidimensional combinatorial substitutions", *Theoretical Computer Science* 454:178–188, 2012, doi:[10.1016/j.tcs.2012.03.050](https://doi.org/10.1016/j.tcs.2012.03.050); numbering of arXiv:1112.1841v2: Section 2 (cells and patterns, substitutions, paths, covers and image vectors, consistency and non-overlapping) and Section 4 (decidability for domino-complete substitutions).
