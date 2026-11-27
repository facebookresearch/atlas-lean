# Barto–Bulín–Krokhin–Opršal: it is NP-hard to (2k−1)-colour a k-colourable graph, in particular to 5-colour a 3-colourable graph

For every $k\ge 3$, $\mathrm{PCSP}(\mathbb{K}_k,\mathbb{K}_{2k-1})$ is NP-hard: given a graph promised to be $k$-colourable, it is NP-hard to find a proper colouring with $2k-1$ colours, and the corresponding decision problem is NP-hard as well. For $k=3$: it is NP-hard to 5-colour a 3-colourable graph, improving the earlier 4-colour bound. The proof also gives NP-hardness of 3-colouring graphs that admit a homomorphism to the 5-cycle $C_5$ (i.e. $\mathrm{PCSP}(C_5,\mathbb{K}_3)$).

## Proof sketch

One shows that $\mathrm{Pol}(\mathbb{K}_3,\mathbb{K}_5)$ admits a minion homomorphism to a minion of bounded essential arity without constants, using a combinatorial analysis of polymorphisms $f:[3]^n\to[5]$ (each such polymorphism has a small set of coordinates that "control" its value on enough tuples); general $k$ follows by a gadget (arc-graph type) reduction between colouring templates. The hardness criterion for bounded essential arity then applies.

## Depends on

- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)

## Proof depends on

- [BBKO hardness criterion: minion homomorphisms to minions of bounded essential arity imply NP-hardness](bbko-bounded-essential-arity-np-hardness.md)
- [Barto–Bulín–Krokhin–Opršal: minion homomorphisms between polymorphism minions give log-space PCSP reductions](bbko-minion-homomorphism-log-space-reduction.md)

## Sources

- Libor Barto, Jakub Bulín, Andrei Krokhin and Jakub Opršal, "Algebraic approach to promise constraint satisfaction", Journal of the ACM 68(4) (2021), arXiv:1811.00970.
