# BBKO hardness criterion: minion homomorphisms to minions of bounded essential arity imply NP-hardness

A coordinate $i$ of $f$ is **essential** if $f$ depends on its $i$-th argument; the **essential arity** of $f$ is the number of essential coordinates. Let $(\mathbb{A},\mathbb{B})$ be a promise template. If there is a minion homomorphism from $\mathrm{Pol}(\mathbb{A},\mathbb{B})$ to a minion $\mathscr{M}$ of functions of bounded essential arity containing no constant function (every member has at least one essential coordinate), then $\mathrm{PCSP}(\mathbb{A},\mathbb{B})$ is NP-hard. In particular this holds when every polymorphism of the pair has essential arity at most a fixed constant $k$ and none is constant.

## Proof sketch

By the minion-homomorphism theorem it suffices to show NP-hardness of $\mathrm{PMC}_{\mathscr{M}}$, which is reduced from Gap Label Cover. Given a Label Cover instance, encode labels by coordinates; a solution of the minor condition in $\mathscr{M}$ assigns to each vertex a function with at most $k$ essential coordinates, and choosing a random essential coordinate decodes a labelling satisfying a $1/k^2$ fraction of constraints, contradicting the PCP-based soundness of Label Cover for large alphabets.

## Depends on

- [The polymorphism minion Pol(A,B) of a promise template](polymorphism-minion-of-a-promise-template.md)
- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)

## Proof depends on

- [Barto–Bulín–Krokhin–Opršal: minion homomorphisms between polymorphism minions give log-space PCSP reductions](bbko-minion-homomorphism-log-space-reduction.md)

## Sources

- Libor Barto, Jakub Bulín, Andrei Krokhin and Jakub Opršal, "Algebraic approach to promise constraint satisfaction", Journal of the ACM 68(4) (2021), arXiv:1811.00970.
