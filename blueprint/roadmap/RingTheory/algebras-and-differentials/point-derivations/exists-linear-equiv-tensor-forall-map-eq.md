# Point derivations of a finite-type algebra are obtained by tensoring

Let $k$ be a field, $A$ a commutative $k$-algebra and $\operatorname{ev} : A \to k$ a $k$-algebra homomorphism. For a $k$-module $M$, a point derivation at $\operatorname{ev}$ with values in $M$ is a $k$-linear map $D : A \to M$ with $D(ab) = \operatorname{ev}(a)\,D(b) + \operatorname{ev}(b)\,D(a)$ for all $a, b \in A$; these form a $k$-submodule $\operatorname{Der}_{\operatorname{ev}}(A, M)$ of $\operatorname{Hom}_k(A, M)$.

Assume $A$ is of finite type over $k$. Then there is a family of $k$-linear isomorphisms

$$
\Psi_M : \operatorname{Der}_{\operatorname{ev}}(A, M) \;\cong\; \operatorname{Der}_{\operatorname{ev}}(A, k) \otimes_k M,
$$

one for each $k$-module $M$ (in the universe of $k$), such that:

1. for all $k$-modules $M, M'$, every $k$-linear map $g : M \to M'$ and every $\delta \in \operatorname{Der}_{\operatorname{ev}}(A, M)$, $\Psi_{M'}(g \circ \delta) = (\mathrm{id} \otimes g)(\Psi_M(\delta))$;
2. for every $\delta \in \operatorname{Der}_{\operatorname{ev}}(A, k)$, $\Psi_k(\delta) = \delta \otimes 1$.
