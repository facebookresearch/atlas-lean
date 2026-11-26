# Lifted product codes over group algebras

Let $\mathcal{R} = \mathbb{F}_2[G]$ for a finite group $G$ and let $A \in \mathcal{R}^{m_A \times n_A}$, $B \in \mathcal{R}^{m_B \times n_B}$. Replacing each entry $r = \sum_g r_g g$ by its $|G| \times |G|$ matrix of right (for $A$) or left (for $B$) multiplication over $\mathbb{F}_2$, the *lifted product* $\mathrm{LP}(A, B)$ is the CSS code with

$$
H_X = \big( A \otimes I_{n_B} \ \big|\ I_{m_A} \otimes B^{*} \big), \qquad H_Z = \big( I_{n_A} \otimes B \ \big|\ A^{*} \otimes I_{m_B} \big),
$$

where $^{*}$ is the conjugate transpose induced by $g \mapsto g^{-1}$, and the tensor products are taken over $\mathcal{R}$; commutation holds because left and right multiplications commute. For $G$ trivial it is the hypergraph product; for $G$ cyclic it yields quasi-cyclic codes.

## Depends on

- [Hypergraph product of two classical codes (Tillich-Zemor)](hypergraph-product-of-classical-codes.md)
- [Balanced products of chain complexes over a group](balanced-product-of-chain-complexes.md)

## Sources

- Pavel Panteleev, Gleb Kalachev, "Quantum LDPC codes with almost linear minimum distance", IEEE Transactions on Information Theory 68(1) (2022); arXiv:2012.04068.
- Pavel Panteleev, Gleb Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022); arXiv:2111.03654.
