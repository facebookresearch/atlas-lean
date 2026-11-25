# Valiant's VP versus VNP conjecture

Fix a field $F$. In an arithmetic circuit over $F$ whose gates are additions and multiplications, the circuit is *multiplicatively disjoint* if the two subcircuits feeding each multiplication gate are disjoint, and *weakly skew* if each multiplication gate $v$ has a child $v'$ such that the edge from $v'$ to $v$ is the only edge from the subcircuit rooted at $v'$ to the rest of the circuit.

- $\mathsf{VP}_F$ is the set of sequences $(f_n)$ of multivariate polynomials over $F$ computed by multiplicatively disjoint circuits of size polynomial in $n$; requiring the circuits to be weakly skew gives $\mathsf{VBP}_F$. Multiplicative disjointness bounds the degree of $f_n$ by the circuit size plus one.
- A sequence $(f_n)$ is in $\mathsf{VNP}_F$ (*p-definable*) if there is $(g_n) \in \mathsf{VP}_F$ with $g_n \in F[x_1, \dots, x_{u(n)}]$ such that for all $n$

    $$f_n(x_1, \dots, x_{v(n)}) = \sum_{e \in \{0,1\}^{u(n) - v(n)}} g_n(x_1, \dots, x_{v(n)}, e_{v(n)+1}, \dots, e_{u(n)}).$$

- A polynomial $f(x_1, \dots, x_n)$ is a *projection* of $g(y_1, \dots, y_m)$ if $f = g(a_1, \dots, a_m)$ for some $a_i \in F \cup \{x_1, \dots, x_n\}$, and $(f_n)$ is a *p-projection* of $(g_m)$ if $f_n$ is a projection of $g_{t(n)}$ for a polynomially bounded $t$. A sequence in a class $\mathcal{C}$ is *$\mathcal{C}$-complete* if every sequence in $\mathcal{C}$ is a p-projection of it.

The determinant family $(\det_n)$ is $\mathsf{VBP}$-complete over every field, and over fields of characteristic other than two the permanent family $(\mathrm{per}_n)$, $\mathrm{per}(A) = \sum_{\pi \in S_n} \prod_{i=1}^n a_{i, \pi(i)}$, is $\mathsf{VNP}$-complete. Clearly $\mathsf{VBP}_F \subseteq \mathsf{VP}_F \subseteq \mathsf{VNP}_F$.

**Valiant's conjecture.** $\mathsf{VP}_F \ne \mathsf{VNP}_F$ for every field $F$.

Over fields of characteristic other than two, the weaker separation $\mathsf{VBP} \ne \mathsf{VNP}$ holds if and only if the permanent family is not a p-projection of the determinant family, that is, if and only if the determinantal complexity of $\mathrm{per}_n$ (the least size of a square matrix of affine linear forms whose determinant is $\mathrm{per}_n$) is not polynomially bounded in $n$. This page states the classes and the conjecture and asserts neither direction.

## Depends on

- [Arithmetic circuit](arithmetic-circuits/arithmetic-circuit.md)

## Sources

- P. Bürgisser, "Completeness classes in algebraic complexity theory", preprint, 2024, <https://arxiv.org/abs/2406.06217>, Definitions 2.1, 2.5, 2.7, 2.9, 2.15, 2.16, 2.25 and 2.35, Theorems 2.20 and 2.29, Corollary 2.33 and the statement of Valiant's conjecture
- Original conjecture: L. G. Valiant, "Completeness classes in algebra", *STOC 1979*. The formulation above follows Bürgisser, who credits the classes, the VNP-completeness of the permanent and the conjecture to Valiant's 1979 conference paper; the VBP-completeness of the determinant is the sharpening by Toda and by Malod and Portier of Valiant's completeness result for the determinant.
