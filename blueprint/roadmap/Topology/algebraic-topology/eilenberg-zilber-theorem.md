# Eilenberg-Zilber theorem: the singular chain complex of X × Y is chain homotopy equivalent to C(X) ⊗ C(Y)

For topological spaces $X$ and $Y$, with $X \times Y$ in the product topology, there are chain maps $\times\colon C_*(X) \otimes C_*(Y) \to C_*(X \times Y)$ and $\theta\colon C_*(X \times Y) \to C_*(X) \otimes C_*(Y)$ between the integral singular chain complexes, natural in $X$ and $Y$, such that in degree $0$ the map $\times$ sends $x \otimes y$ to the point $(x, y)$ and $\theta$ sends $(x,y)$ to $x \otimes y$. These maps are chain homotopy inverse to each other.

## Proof sketch

Use acyclic models on the category of pairs of spaces. The functor $(X, Y) \mapsto C_n(X \times Y)$ is free on the models $(\Delta^n, \Delta^n)$ (diagonal simplices), and $(X,Y) \mapsto (C(X) \otimes C(Y))_n$ is free on the models $(\Delta^p, \Delta^q)$, $p + q = n$. Both are acyclic on models: $\Delta^p \times \Delta^q$ is contractible, so its singular homology is $\mathbb{Z}$ in degree $0$ and zero otherwise, and the algebraic Künneth formula gives the same for $C(\Delta^p) \otimes C(\Delta^q)$. The acyclic models theorem then yields natural chain maps both ways extending the degree-$0$ maps determined by the augmentations on the point model, and shows that both composites are naturally chain homotopic to the identity.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: Acyclic models theorem; Algebraic Künneth formula; chain homotopy equivalences; the product topology; Singular chain groups and boundary homomorphisms of a topological space $X$; Tensor product $C \otimes C'$ of chain complexes of abelian groups.

## Proof depends on

- [A contractible space has trivial reduced singular homology](singular-homology/contractible-reduced-homology-vanishes.md)

## Sources

- James R. Munkres, Elements of Algebraic Topology, Addison-Wesley, 1984.
