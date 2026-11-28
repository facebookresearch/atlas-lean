# Positivity of a translation-invariant MPDO for all system sizes is undecidable

No algorithm decides, for seven given $7 \times 7$ integer matrices, whether the periodic, diagonal matrix product density operator they define is positive semidefinite for every system size, or eventually fails to be, even under the promise that one of these two cases holds.

**Problem.** Given integer matrices $A_1, \dots, A_7 \in \mathbb{Z}^{7 \times 7}$, consider the operators $\rho_A^L$, $L \geq 1$, of the [periodic diagonal matrix product density operator](periodic-diagonal-matrix-product-density-operators.md) they define. One is promised that exactly one of the following holds:

1. $\rho_A^L \geq 0$ for all $L$;
2. there is an $L_0$ such that $\rho_A^L \not\geq 0$ for all $L \geq L_0$.

The problem is to decide which case holds.

**Theorem (De las Cuevas, Cubitt, Cirac, Wolf and Pérez-García).** This promise problem is undecidable (Problem 2 and Lemma 3 of the source).

In particular no algorithm decides, given $A_1, \dots, A_7$, whether $\rho_A^L \geq 0$ for all $L$. The source uses this to show that some families of such operators that are positive for every $L$ have no translation-invariant purification valid for all $L$ (Theorem 1 of the source).

## Depends on

- [Periodic diagonal matrix product density operators](periodic-diagonal-matrix-product-density-operators.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A good expansion links a page for the zero-in-the-upper-left-corner problem, which the proof reduces: given five integer $3 \times 3$ matrices $Y_1, \dots, Y_5$, is there a nonempty product $Y_{j_1} \cdots Y_{j_m}$ with $\langle 0 \rvert Y_{j_1} \cdots Y_{j_m} \lvert 0\rangle = 0$? The source quotes Cassaigne, Halava, Harju and Nicolas for its undecidability under the promise that the matrices can be put in upper triangular form simultaneously by one non-singular matrix, naming no field (proof of Lemma 3 of arXiv:1512.05709v2). Their instances satisfy it with one common rational change of basis: their matrices $\Psi(u, v)$ are rational and upper triangular (Lemma 7, Equation (1), and Theorem 1 of arXiv:1404.0644v2), and the reduction to the upper-left corner conjugates them all by one rational matrix (Proposition 2 there). A complex change of basis would not do: the step below needs the eigenvalues of every product to be real. Let $V$ be the $9 \times 6$ integer matrix whose columns are the basis $\lvert jj\rangle$ ($0 \leq j \leq 2$) and $\lvert jk\rangle + \lvert kj\rangle$ ($0 \leq j < k \leq 2$) of the symmetric subspace of $\mathbb{C}^3 \otimes \mathbb{C}^3$, and $V^{+} = (V^{\mathsf{T}} V)^{-1} V^{\mathsf{T}}$, with entries $0$, $1$ and $\tfrac12$. Since $Y \otimes Y$ preserves the symmetric subspace, $S(Y) = V^{+} (Y \otimes Y) V$ is the matrix of its restriction in this basis; it has integer entries, because the coordinate of a symmetric vector at $\lvert jk\rangle + \lvert kj\rangle$ is its $\lvert jk\rangle$ entry. Let $E$ be the $6 \times 6$ matrix unit at the basis vector $\lvert 00\rangle$, the matrix of $\lvert 00\rangle\langle 00\rvert$ in the same basis, and put

$$
A_i = S(Y_i) \oplus (1) \quad (i \leq 5), \qquad A_6 = E \oplus (1), \qquad A_7 = E \oplus (-1).
$$

The source writes $S(Y_i)$ with a real isometry onto the symmetric subspace, which is conjugate to $S(Y_i)$ by one fixed matrix and so gives the same traces of products, but whose entries need not be rational. For a word without $6$ or $7$, with product $Y$, the trace is $\tfrac12[(\operatorname{tr} Y)^2 + \operatorname{tr}(Y^2)] + 1 > 0$; here the common real triangular form makes the diagonal of $Y$ real, so $\operatorname{tr}(Y^2) \geq 0$. For a word with $k \geq 1$ letters $6$ or $7$, cut cyclically at these letters into blocks with products $Y^{(1)}, \dots, Y^{(k)}$ (an empty block giving the identity); then the trace is $\prod_{l=1}^{k} \bigl(\langle 0 \rvert Y^{(l)} \lvert 0\rangle\bigr)^2 + (-1)^{\#7}$, where $\#7$ is the number of letters $7$. If some corner entry $\langle 0 \rvert Y_{j_1} \cdots Y_{j_m} \lvert 0\rangle$ vanishes, the word $j_1 \cdots j_m\, 7\, 6^{s}$ has trace $-1$ for every $s \geq 0$, so Case 2 holds. If no corner entry vanishes, every corner entry is a nonzero integer, the product of squares is at least $1$, every trace is nonnegative, and Case 1 holds.

## Sources

- G. De las Cuevas, T. S. Cubitt, J. I. Cirac, M. M. Wolf and D. Pérez-García, "Fundamental limitations in the purifications of tensor networks", *Journal of Mathematical Physics* 57(7), 071902, 2016, doi:[10.1063/1.4954983](https://doi.org/10.1063/1.4954983). Numbering of the version read, arXiv:1512.05709v2: Problem 2, Lemma 3 and its proof (Equations (5)–(13)), and Theorem 1 (no purification for all system sizes).
- J. Cassaigne, V. Halava, T. Harju and F. Nicolas, "Tighter undecidability bounds for matrix mortality, zero-in-the-corner problems, and more", arXiv:1404.0644v2 ([arXiv](https://arxiv.org/abs/1404.0644v2)), the version the first source cites for the zero-in-the-upper-left-corner problem; read only for the form of its instances: Lemma 7 and Equation (1), Theorem 1 and Proposition 2.
