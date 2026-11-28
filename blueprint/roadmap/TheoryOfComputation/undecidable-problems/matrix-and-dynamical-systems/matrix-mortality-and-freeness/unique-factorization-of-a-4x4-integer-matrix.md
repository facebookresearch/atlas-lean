# Unique factorization in semigroups of 4×4 integer matrices is undecidable

No algorithm decides, given finitely many $4 \times 4$ integer matrices and a matrix $M$ in the semigroup they generate, whether $M$ can be written as a product of generators in more than one way.

**Theorem (Ko and Potapov).** Let $G = \{M_1, \dots, M_n\} \subseteq \mathbb{Z}^{4 \times 4}$ be a finite set of matrices and $S = \langle G \rangle$ the semigroup they generate under matrix multiplication. A *factorization* of $M \in S$ over $G$ is a finite nonempty sequence $(i_1, \dots, i_k)$ of indices with $M = M_{i_1} M_{i_2} \cdots M_{i_k}$. There is no algorithm that decides, given $G$ and a matrix $M \in S$, whether $M$ has more than one factorization over $G$ (Theorem 13 of the source). This is a promise problem: inputs are pairs with $M \in S$, as in the source's Problem 3, and no answer is required for $M \notin S$; all entries are integers, so instances are finite.

The same problem for matrices in $\mathrm{SL}(2, \mathbb{Z})$ is decidable (and [NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)-hard), by representing the matrices equal to $M$ as a [context-free language](../../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md) of words and counting the factorizations of the words it shares with the generator language (Theorem 12 of the source). Deciding whether a given matrix has infinitely many factorizations, the recurrent matrix problem, is undecidable over $\mathbb{Z}^{4 \times 4}$ (Bell and Potapov) but decidable in $\mathrm{SL}(2, \mathbb{Z})$ (Theorem 15).

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the *fixed element Post correspondence problem* (FEPCP) of Bell and Potapov: over the alphabet $\Gamma = \{a, b, a^{-1}, b^{-1}, \Delta, \Delta^{-1}, \star\}$, where $\Gamma \setminus \{\star\}$ generates a free group, and a finite set $P = \{(u_1, v_1), \dots, (u_n, v_n)\}$ of pairs of words over $\Gamma$, is there a nonempty index sequence $s_1, \dots, s_k$ with $u_{s_1} \cdots u_{s_k} = v_{s_1} \cdots v_{s_k} = \star$ in the free group? This problem is undecidable by a reduction from the Post correspondence problem. A homomorphism $\gamma$ maps the letters of $\Gamma$ injectively into $\mathrm{SL}(2, \mathbb{Z})$ through the classical embedding of the free group on two generators, and each pair gives the block-diagonal matrix $A_i = \mathrm{diag}(\gamma(u_i), \gamma(v_i)) \in \mathbb{Z}^{4 \times 4}$. Let $B = \mathrm{diag}(\gamma(\star), \gamma(\star))$ and $G = \{A_1, \dots, A_n, B\}$. The matrix $B$ always has the factorization consisting of $B$ alone, and it has a second factorization exactly when some product of the $A_i$ equals $B$, that is, exactly when the FEPCP instance has a solution.

## Sources

- Sang-Ki Ko and I. Potapov, "Matrix Semigroup Freeness Problems in SL(2, ℤ)", in *SOFSEM 2017: Theory and Practice of Computer Science*, Lecture Notes in Computer Science 10139, Springer, 2017, pp. 268–279, doi:[10.1007/978-3-319-51963-0_21](https://doi.org/10.1007/978-3-319-51963-0_21); read as arXiv:1610.09834v1, whose numbering is used here: Theorem 13 with its proof (reduction from FEPCP), Theorem 12 and Theorem 15.
- P. C. Bell and I. Potapov, "Periodic and infinite traces in matrix semigroups", in *SOFSEM 2008: Theory and Practice of Computer Science*, Lecture Notes in Computer Science 4910, Springer, 2008, pp. 148–161, doi:[10.1007/978-3-540-77566-9_13](https://doi.org/10.1007/978-3-540-77566-9_13); not read directly here: the fixed element PCP and the recurrent matrix problem rest on their statement in the arXiv copy of the first source above (proof of Theorem 13 and the paragraph before Theorem 15).
