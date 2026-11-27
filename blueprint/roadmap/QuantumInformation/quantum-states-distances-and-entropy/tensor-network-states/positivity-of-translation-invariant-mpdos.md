# Positivity of a translation-invariant MPDO for all system sizes is undecidable

No algorithm decides, for seven given $7 \times 7$ integer matrices, whether the periodic, diagonal matrix product density operator they define is positive semidefinite for every system size, or eventually fails to be, even under the promise that one of these two cases holds.

**Problem.** Given integer matrices $A_1, \dots, A_7 \in \mathbb{Z}^{7 \times 7}$, consider the operators $\rho_A^L$ of the periodic, diagonal [translation-invariant matrix product operator](translation-invariant-matrix-product-operators.md) they define, $L \geq 1$. One is promised that exactly one of the following holds:

1. $\rho_A^L \geq 0$ for all $L$;
2. there is an $L_0$ such that $\rho_A^L \not\geq 0$ for all $L \geq L_0$.

The problem is to decide which case holds.

**Theorem (De las Cuevas, Cubitt, Cirac, Wolf and Pérez-García).** This promise problem is undecidable.

In particular no algorithm decides, given $A_1, \dots, A_7$, whether $\rho_A^L \geq 0$ for all $L$. The source uses this to show that some families of such operators that are positive for every $L$ have no translation-invariant purification valid for all $L$.

## Depends on

- [Translation-invariant matrix product operators](translation-invariant-matrix-product-operators.md)
- [Polynomial-time reduction between promise problems](../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the zero-in-the-upper-left-corner problem: given five integer $3 \times 3$ matrices $Y_1, \dots, Y_5$, is there a product $Y_{j_1} \cdots Y_{j_m}$ with $\langle 0 \rvert Y_{j_1} \cdots Y_{j_m} \lvert 0\rangle = 0$? The source quotes Cassaigne, Halava, Harju and Nicolas for its undecidability, even under the promise that the matrices can be put in upper triangular form simultaneously. Let $P$ be the projector onto the symmetric subspace of $\mathbb{C}^3 \otimes \mathbb{C}^3$ and $\mathcal{O}$ a real $6 \times 9$ isometry with $\mathcal{O}^\dagger\mathcal{O} = P$. Put

$$
A_i = \mathcal{O} P (Y_i \otimes Y_i) P \mathcal{O}^\dagger \oplus \lvert 6\rangle\langle 6\rvert \quad (i \leq 5), \qquad A_6 = \lvert 00\rangle\langle 00\rvert \oplus \lvert 6\rangle\langle 6\rvert, \qquad A_7 = \lvert 00\rangle\langle 00\rvert \oplus (-\lvert 6\rangle\langle 6\rvert),
$$

with rational entries; clearing denominators gives integer matrices. If $\langle 0 \rvert Y_{j_1} \cdots Y_{j_m} \lvert 0\rangle = 0$, the word $j_1 \cdots j_m 7$ has trace $(\langle 0 \rvert Y_{j_1} \cdots Y_{j_m} \lvert 0\rangle)^2 - 1 = -1$, and appending letters $6$ keeps the trace negative at every larger length. Conversely, a word without $6$ or $7$ has trace $\tfrac12[(\operatorname{tr} Y)^2 + \operatorname{tr}(Y^2)] + 1 > 0$ for the product $Y$ (here the simultaneous triangular form makes $\operatorname{tr}(Y^2) \geq 0$), a single $6$ gives a square plus $1$, and a single $7$ gives a square minus $1$, which is negative only when the integer corner entry vanishes. So the instance falls in Case 2 exactly when some corner entry vanishes, and in Case 1 otherwise.

## Sources

- G. De las Cuevas, T. S. Cubitt, J. I. Cirac, M. M. Wolf and D. Pérez-García, "Fundamental limitations in the purifications of tensor networks", *Journal of Mathematical Physics* 57(7), 071902, 2016, doi:[10.1063/1.4954983](https://doi.org/10.1063/1.4954983). Numbering of the version read, arXiv:1512.05709v2: Problem 2, Lemma 3 and its proof, and Theorem 1 (no purification for all system sizes).
