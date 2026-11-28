# Positivity of all matrix moments over noncommutative polynomial rings is undecidable

No algorithm decides whether every moment $\operatorname{tr}(A^n)$ of a given square matrix over $\mathbb{Z}\langle z_1, \dots, z_d\rangle$ has nonnegative coefficients, for $d, s \ge 7$.

**Setting (De les Coves, Graf, Klingler and Netzer).** Let $\mathcal{R}$ be a unital ring, not necessarily commutative, and $A \in \operatorname{Mat}_s(\mathcal{R})$. The $n$-th *moment* of $A$ is $\mu_n(A) = \operatorname{tr}(A^n) \in \mathcal{R}$. For a fixed subset $\mathcal{P} \subseteq \mathcal{R}$ and a fixed size $s$, the *moment membership problem* asks, given $A \in \operatorname{Mat}_s(\mathcal{R})$, whether $\mu_n(A) \in \mathcal{P}$ for all $n \ge 0$, where $\mu_0(A) = s \cdot 1$. For polynomial rings over $\mathbb{Z}$, $\mathcal{P}_{\mathrm{coeff}}$ is the set of polynomials all of whose coefficients are nonnegative.

**Theorem (De les Coves, Graf, Klingler and Netzer).** Let $d, s \ge 7$. The moment membership problem for $\mathcal{R} = \mathbb{Z}\langle z_1, \dots, z_d\rangle$, the ring of noncommutative polynomials, with $\mathcal{P} = \mathcal{P}_{\mathrm{coeff}}$ and size $s$ is undecidable. This remains true for inputs $A$ whose entries are linear forms in $z_1, \dots, z_d$ (Theorem 24 of arXiv:2404.15053v2).

For commutative polynomial rings the source proves (Theorem 20, about Problem 19): for $s$ and $d$ large enough and a suitably chosen fixed matrix $M \in \operatorname{Mat}_s(\mathbb{Z}[x_1, \dots, x_d])$, it is undecidable, given $A \in \operatorname{Mat}_s(\mathbb{Z}[x_1, \dots, x_d])$, whether $\operatorname{tr}(A^n M) \in \mathcal{P}_{\mathrm{coeff}}$ for all $n \ge 1$.

In the theorem the cone $\mathcal{P}_{\mathrm{coeff}}$ coincides with the polynomials taking entrywise nonnegative values on all tuples of nonnegative integer matrices (a free Pólya theorem, Theorem 22 of the source). Theorem 20 shows that positivity of linear recurrence sequences over $\mathbb{Z}[x_1, \dots, x_d]$ is undecidable in general. Whether the problem is decidable for $\mathcal{R} = \mathbb{Q}$ with $\mathcal{P} = [0, \infty)$, closely related to the positivity problem for linear recurrence sequences, is the central open question of the source, and the source proves decidability for several classes of matrices, among them orthogonal and unitary ones.

## Depends on

- [Ring with identity](../../../Algebra/rings-and-fields/ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

For the theorem, a linear input $A = \sum_k z_k A_k$ with $A_k \in \operatorname{Mat}_s(\mathbb{Z})$ has $\mu_n(A) = \sum \operatorname{tr}(A_{k_1} \cdots A_{k_n})\, z_{k_1} \cdots z_{k_n}$, so all moments lie in $\mathcal{P}_{\mathrm{coeff}}$ exactly when every product of the $A_k$ has nonnegative trace, which is undecidable for $d, s \ge 7$ by a lemma of De las Cuevas, Cubitt, Cirac, Wolf and Pérez-García. For Theorem 20, the source reduces (Lemma 16) from a version of matrix mortality, whether $A_1^{n_1} \cdots A_d^{n_d} = 0$ for some exponents, which is undecidable for large $s$ and $d$ (Bell, Halava, Harju, Karhumäki and Potapov, *International Journal of Algebra and Computation* 18:1231–1241, 2008): squaring the entries through $X \otimes X$ gives a fixed matrix $N$ with $\operatorname{tr}(\cdots N) < 0$ exactly at a zero product, and a block upper-triangular matrix $A$ with blocks $A_i x_i$ turns the exponents into monomials. A good expansion adds and links pages for the trace-positivity lemma for products of integer matrices and for the undecidability of this version of matrix mortality.

## Sources

- G. De les Coves, J. Graf, A. Klingler and T. Netzer, "Positive moments forever: Undecidable and decidable cases", *Linear Algebra and its Applications* 722:255–275, 2025, doi:[10.1016/j.laa.2025.05.015](https://doi.org/10.1016/j.laa.2025.05.015); read as arXiv:2404.15053v2 ([arXiv](https://arxiv.org/abs/2404.15053v2)), whose numbering is used (one global counter): the moment membership problem of Section 2, Lemma 16, Theorems 20, 22 and 24 in Section 4, and the conclusion.
