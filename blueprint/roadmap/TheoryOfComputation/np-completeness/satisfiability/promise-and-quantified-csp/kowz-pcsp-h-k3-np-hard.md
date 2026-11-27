# Krokhin–Opršal–Wrochna–Živný: PCSP(H, K3) is NP-hard for every non-bipartite 3-colourable graph H

For every non-bipartite loopless graph $H$ with $H\to\mathbb{K}_3$, $\mathrm{PCSP}(H,\mathbb{K}_3)$ is NP-hard; equivalently, for every odd $k\ge 3$ it is NP-hard to 3-colour a graph that admits a homomorphism to the odd cycle $C_k$. More generally, if $H\to G$ are non-bipartite loopless graphs and there is a $\mathbb{Z}_2$-equivariant continuous map from the geometric realization $|\mathrm{Hom}(K_2,G)|$ of the homomorphism complex to the circle $S^1$ (with the antipodal action), then $\mathrm{PCSP}(H,G)$ is NP-hard. This applies to circular cliques $K_{p/q}$ with $2 < p/q < 4$ and to all square-free graphs $G$, confirming the Brakensiek–Guruswami conjecture (that $\mathrm{PCSP}(H,G)$ is NP-hard for all non-bipartite loopless $H\to G$) for square-free $G$.

## Proof sketch

Polymorphisms $C_k^n\to G$ induce $\mathbb{Z}_2$-maps between homomorphism complexes; composing with the assumed map to $S^1$ assigns to every polymorphism an odd-degree map on a torus, whose homological degree data define a minion homomorphism into a minion of bounded essential arity (in fact into the minion of "parity of degrees" functions). The bounded-essential-arity hardness criterion then gives NP-hardness.

## Depends on

- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)

## Proof depends on

- [BBKO hardness criterion: minion homomorphisms to minions of bounded essential arity imply NP-hardness](bbko-bounded-essential-arity-np-hardness.md)
- [Barto–Bulín–Krokhin–Opršal: minion homomorphisms between polymorphism minions give log-space PCSP reductions](bbko-minion-homomorphism-log-space-reduction.md)

## Sources

- Andrei Krokhin, Jakub Opršal, Marcin Wrochna and Stanislav Živný, "Topology and adjunction in promise constraint satisfaction", SIAM Journal on Computing 52(1) (2023), arXiv:2003.11351.
