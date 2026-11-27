# Two unimodular matrices generate a free monoid

The two elementary $2 \times 2$ integer matrices with a single off-diagonal $1$ generate a free monoid of rank two, consisting of all $2 \times 2$ matrices with natural-number entries and determinant $1$.

Let

$$
P = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}, \qquad Q = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix} .
$$

The monoid morphism $\{a, b\}^* \to \mathrm{SL}(2, \mathbb{Z})$ with $a \mapsto P$ and $b \mapsto Q$ is injective, and its image is the set of matrices in $\mathrm{SL}(2, \mathbb{Z})$ whose four entries are natural numbers. Consequently a word equation over $\{a, b\}$ in unknowns $x_1, \dots, x_n$ has a solution exactly when the system of polynomial equations obtained by replacing each $x_i$ by a matrix of four unknowns ranging over $\mathbb{N}$ with determinant $1$ and equating the four entries of the two products has a solution.

## Depends on

None.

## Proof depends on

None.

## Expansion

Right multiplication by $P$ adds the first column to the second, and by $Q$ the second column to the first; so a product ending in $P$ has its second column dominating its first entrywise, and a product ending in $Q$ has its first column dominating its second. Let $M = \begin{pmatrix} p & q \\ r & s \end{pmatrix}$ have natural entries, $ps - qr = 1$ and $M \neq I$. If neither column dominated the other, then either $p > q$ and $s > r$, which gives $ps \ge (q + 1)(r + 1)$, hence $1 = ps - qr \ge q + r + 1$, so $q = r = 0$, $p = s = 1$ and $M = I$; or $p < q$ and $s < r$, which gives $ps < qr$, impossible. Both columns cannot dominate, since then $p = q$ and $r = s$ and the determinant is $0$. So exactly one column dominates, say the second; then $M P^{-1} = \begin{pmatrix} p & q - p \\ r & s - r \end{pmatrix}$ again has natural entries and determinant $1$, and its entry sum is smaller by $p + r \ge 1$. By induction on the entry sum, every such matrix is a product of $P$ and $Q$, and the product is unique because its last factor is determined by which column dominates. This gives the description of the image and injectivity.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Section 6 (Notes), which states that the matrices with natural entries and determinant $1$ form a free monoid on these two generators and gives the Diophantine encoding
- Volker Diekert, "More Than 1700 Years of Word Equations", Algebraic Informatics (CAI 2015), LNCS 9270, 22–28 (2015), https://doi.org/10.1007/978-3-319-23021-4_2; read as arXiv:1507.03215v1, https://arxiv.org/abs/1507.03215v1, Section "History"
