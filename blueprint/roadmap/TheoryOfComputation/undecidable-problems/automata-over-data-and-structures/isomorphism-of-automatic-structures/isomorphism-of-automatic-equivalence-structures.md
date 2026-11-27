# Isomorphism of automatic equivalence structures is Π⁰₁-complete

Whether two automatic presentations describe isomorphic equivalence structures is a co-recursively-enumerable-complete problem, so it is undecidable.

**Theorem.** An *equivalence structure* is a structure $(D; E)$ with $E$ an equivalence relation on $D$. The isomorphism problem for [automatic](automatic-structure.md) equivalence structures, which asks, given automatic presentations $P_1, P_2$ of equivalence structures, whether $S(P_1) \cong S(P_2)$, is complete for the class [$\Pi^0_1$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md) of the arithmetical hierarchy. In fact there is a single automatic equivalence structure $E_{\mathrm{Good}}$ such that the set of automatic presentations $P$ with $S(P) \cong E_{\mathrm{Good}}$ is $\Pi^0_1$-hard (Proposition 4 of the source).

The construction turns an equivalence structure into a tree of height $2$ (a root, one child per class, and the elements of each class below it), so the isomorphism problem for automatic trees of height at most $2$ is $\Pi^0_1$-hard as well (Corollary 6).

## Depends on

- [Automatic structure](automatic-structure.md)
- [Arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Equivalence relation](../../../../Order/ordered-sets/equivalence-relation.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

*Membership.* For an automatic equivalence structure $E$ let $h_E(n)$ be the number of classes of size $n \in \mathbb N \cup \{\aleph_0\}$. Each value $h_E(n)$ is computable from a presentation, because "there are exactly $k$ classes of size $n$" and "there are infinitely many" are expressible in first-order logic with the quantifier "there exist infinitely many", whose theory is decidable on automatic structures. Two countable equivalence structures are isomorphic iff $h_{E_1} = h_{E_2}$, a $\Pi^0_1$ condition.

*Hardness.* The proof reduces the complement of Hilbert's tenth problem, in the form: given nonzero polynomials $p_1, p_2 \in \mathbb N[x_1, \dots, x_k]$, is $p_1(c) \neq p_2(c)$ for all $c \in \mathbb N_+^k$? For a polynomial $S$, a counting construction with automata (Lemmas 2 and 3) gives an automatic equivalence structure whose class sizes are exactly the values of $S$ on $\mathbb N_+^k$, each class size occurring infinitely often. With an injective polynomial pairing $C(y, z)$, take $\aleph_0$ copies of the structures for $C(p_1, p_2)$, $C(x_1 + x_2, x_1)$ and $C(x_1, x_1 + x_2)$; the result has a class of size $C(y, y)$ iff $p_1(c) = p_2(c)$ for some $c$, and is otherwise isomorphic to the structure $E_{\mathrm{Good}}$ having infinitely many classes of each size $C(y, z)$ with $y \neq z$ and no others.

## Sources

- D. Kuske, J. Liu and M. Lohrey, "The Isomorphism Problem on Classes of Automatic Structures", in *Proceedings of the 25th Annual IEEE Symposium on Logic in Computer Science (LICS 2010)*, IEEE Computer Society, 2010, pp. 160–169, doi:[10.1109/LICS.2010.10](https://doi.org/10.1109/LICS.2010.10); read as arXiv:1001.2086v1, whose numbering is used here: Section 3 (the function $h_E$, Lemmas 2 and 3, Proposition 4, Theorem 5) and Corollary 6.
