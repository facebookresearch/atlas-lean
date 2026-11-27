# SL = L

Symmetric logarithmic space collapses to deterministic logarithmic space: $\mathsf{SL}=\mathsf{L}$. Equivalently, $\mathrm{USTCON}\in\mathsf{L}$ (and then $\mathrm{USTCON}$ is $\mathsf{L}$-complete under logspace many-one reductions, as every language in $\mathsf{L}$ other than $\emptyset$ and $\{0,1\}^*$ is).

## Proof sketch

Reingold's theorem places $\mathrm{USTCON}$ in $\mathsf{L}$, and $\mathsf{L}$ is closed under logspace many-one reductions; the reverse inclusion holds because any $L\in\mathsf{L}$ maps to a trivial yes- or no-instance of USTCON.

## Depends on

- [Symmetric logarithmic space SL](symmetric-logspace.md)
- [Deterministic logarithmic space](../../../time-and-space-complexity-classes/log-space.md)

## Proof depends on

- [Undirected ST-connectivity is in L (Reingold)](../../../../polynomial-time-problems/undirected-s-t-connectivity/ustcon-in-l.md)
- [Log-space computable functions](../../../time-and-space-complexity-classes/log-space-computable.md)
- [Logarithmic-space computable functions compose](../logspace-composition-and-layered-reachability/logspace-functions-compose.md)

## Sources

- Omer Reingold, "Undirected Connectivity in Log-Space", Journal of the ACM 55(4), 2008.
- Harry R. Lewis and Christos H. Papadimitriou, "Symmetric Space-Bounded Computation", Theoretical Computer Science 19(2), 1982.
