# Naturality of the tensor description of point derivations

Let $k$ be a field, $A$ a commutative $k$-algebra and $\operatorname{ev} : A \to k$ a $k$-algebra homomorphism. For a $k$-module $M$, a point derivation at $\operatorname{ev}$ with values in $M$ is a $k$-linear map $D : A \to M$ with $D(ab) = \operatorname{ev}(a)\,D(b) + \operatorname{ev}(b)\,D(a)$ for all $a, b \in A$; these form a $k$-submodule $\operatorname{Der}_{\operatorname{ev}}(A, M)$ of $\operatorname{Hom}_k(A, M)$.

Assume $A$ is of finite type over $k$, and write $\Psi_M : \operatorname{Der}_{\operatorname{ev}}(A, M) \cong \operatorname{Der}_{\operatorname{ev}}(A, k) \otimes_k M$ for the canonical isomorphism. For $k$-modules $M, M'$, a $k$-linear map $g : M \to M'$ and $\delta \in \operatorname{Der}_{\operatorname{ev}}(A, M)$,

$$
\Psi_{M'}(g \circ \delta) = (\mathrm{id} \otimes g)\bigl(\Psi_M(\delta)\bigr).
$$
