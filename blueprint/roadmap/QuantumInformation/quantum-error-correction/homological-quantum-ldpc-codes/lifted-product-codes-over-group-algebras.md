# Lifted product codes over group algebras

Let $\mathcal{R} = \mathbb{F}_2[G]$ for a finite group $G$ and let $A \in \mathcal{R}^{m_A \times n_A}$, $B \in \mathcal{R}^{m_B \times n_B}$. Regard $A$ as a two-term complex $\mathcal{A} : \mathcal{R}^{n_A} \to \mathcal{R}^{m_A}$ of right $\mathcal{R}$-modules and $B$ as a two-term complex $\mathcal{B} : \mathcal{R}^{n_B} \to \mathcal{R}^{m_B}$ of left $\mathcal{R}$-modules. The *lifted product* $\mathrm{LP}(A, B)$ is the CSS code of the tensor complex $\mathcal{A} \otimes_{\mathcal{R}} \mathcal{B}$,

$$
\mathcal{R}^{n_A n_B} \xrightarrow{\ \partial_2\ } \mathcal{R}^{n_A m_B} \oplus \mathcal{R}^{m_A n_B} \xrightarrow{\ \partial_1\ } \mathcal{R}^{m_A m_B},
$$

with qubits in the middle term. Replacing each entry $r = \sum_g r_g g$ of $A$ and of $B$ by the $|G| \times |G|$ matrix over $\mathbb{F}_2$ of multiplication by $r$, taken on opposite sides for $A$ and for $B$ so that every block of $\hat A$ commutes with every block of $\hat B$, the parity-check matrices are

$$
H_X = \partial_1 = \big( \hat A \otimes I_{m_B} \ \big|\ I_{m_A} \otimes \hat B \big), \qquad H_Z = \partial_2^{*} = \big( I_{n_A} \otimes \hat B^{*} \ \big|\ \hat A^{*} \otimes I_{n_B} \big),
$$

where $^{*}$ is the transpose (for group-algebra entries, induced by $g \mapsto g^{-1}$) and the Kronecker products are taken blockwise over $\mathcal{R}$. The code has $n = |G|(n_A m_B + m_A n_B)$ qubits, and $H_X H_Z^{*} = \hat A \otimes \hat B + \hat A \otimes \hat B = 0$ over $\mathbb{F}_2$ because the blocks commute. For $G$ trivial it is the hypergraph product of $\ker A$ and $\ker B$; for $G$ cyclic it yields quasi-cyclic codes. The product with the dual complex $\mathcal{B}^{*} : \mathcal{R}^{m_B} \to \mathcal{R}^{n_B}$, given by $B^{*}$, is a different code $\mathrm{LP}(A, B^{*})$ with $|G|(n_A n_B + m_A m_B)$ qubits; for $1 \times 2$ matrices over the trivial group the two have $4$ and $5$ qubits respectively.

## Depends on

- [Hypergraph product of two classical codes (Tillich-Zemor)](hypergraph-product-of-classical-codes.md)
- [Balanced products of chain complexes over a group](balanced-product-of-chain-complexes.md)

## Sources

- Pavel Panteleev, Gleb Kalachev, "Quantum LDPC codes with almost linear minimum distance", IEEE Transactions on Information Theory 68(1) (2022); arXiv:2012.04068.
- Pavel Panteleev, Gleb Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022); arXiv:2111.03654, Section 1 and Appendix B.
