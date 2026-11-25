# Cluster algebras of rank two

For positive integers $b$ and $c$, the coefficient-free cluster algebra $\mathcal{A}(b, c)$ of rank
two has exchange matrices $\pm\begin{pmatrix} 0 & b \\ -c & 0 \end{pmatrix}$, and its cluster
variables $\dots, z_1, z_2, z_3, \dots$ satisfy $z_{k-1} z_{k+1} = z_k^c + 1$ for even $k$ and
$z_k^b + 1$ for odd $k$ (Fomin, Williams and Zelevinsky, *Introduction to cluster algebras, Chapters
1–3*, arXiv:1608.05735v5, equation (3.2.2)). When $bc \le 3$ the sequence is periodic with period
$h + 2$, where $h = 3, 4, 6$ is the Coxeter number of the root system $A_2$, $B_2$, $G_2$ with
Cartan matrix $\begin{pmatrix} 2 & -b \\ -c & 2 \end{pmatrix}$, so there are finitely many cluster
variables; when $bc \ge 4$ the sequence is not periodic. At $z_1 = z_2 = 1$ the terms of
$\mathcal{A}(1, 4)$ take the values $2, 3, 41, 14, 937, \dots$, and these values are integers, as
the Laurent phenomenon predicts (Examples 3.2.4, 3.2.7 and 3.2.10; Fomin and Zelevinsky, *Cluster
algebras I*, J. Amer. Math. Soc. 15 (2002), Theorem 6.1 and Proposition 6.2, which also identify the
denominators with the positive roots).

The recurrence makes sense over any field, where it is the sequence of alternating seed mutations of
the exchange matrix $\begin{pmatrix} 0 & b \\ -c & 0 \end{pmatrix}$. As long as no term vanishes,
which holds for positive real initial values, the cluster variables of types $A_2$, $B_2$ and $G_2$
are explicit Laurent polynomials in the initial cluster and are periodic with periods $5$, $6$ and
$8$. The rank-two Laurent phenomenon for all $b, c > 0$ is part of [Seed mutation and the Laurent
phenomenon](../seed-mutation-and-the-laurent-phenomenon/README.md).

- [Rank-two exchange recurrence](rank-two-seq.md)
- [Exchange relation of the rank-two recurrence](rank-two-seq-mul-add-two.md)
- [Positivity of the rank-two recurrence](rank-two-seq-pos.md)
- [Exchange matrix of $\mathcal{A}(b, c)$](rank-two-matrix.md)
- [The exchange matrix of $\mathcal{A}(b, c)$ is skew-symmetrizable](is-skew-symmetrizable-rank-two-matrix.md)
- [Seed mutation in rank two is the rank-two recurrence](mutate-seq-rank-two-matrix.md)
- [Cluster variables of type $A_2$](rank-two-seq-one-one-laurent.md)
- [Five-periodicity in type $A_2$](rank-two-seq-one-one-periodic.md)
- [Cluster variables of type $B_2$](rank-two-seq-one-two-laurent.md)
- [Six-periodicity in type $B_2$](rank-two-seq-one-two-periodic.md)
- [Cluster variables of type $G_2$](rank-two-seq-one-three-laurent.md)
- [Eight-periodicity in type $G_2$](rank-two-seq-one-three-periodic.md)

## Related topics

- [Seed mutation and the Laurent phenomenon](../seed-mutation-and-the-laurent-phenomenon/README.md): the general exchange relations, of which the rank-two recurrence is the case $n = 2$.
- [Finite type criterion for cluster algebras](../finite-cluster-variables-iff.md): rank two is the base case of the criterion $|b_{ij} b_{ji}| \le 3$.
