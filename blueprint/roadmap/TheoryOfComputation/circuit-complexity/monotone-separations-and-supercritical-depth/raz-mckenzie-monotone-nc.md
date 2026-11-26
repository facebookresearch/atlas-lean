# Raz–McKenzie: separation of the monotone NC hierarchy

For every $i \ge 1$, $\mathrm{monotone}\text{-}\mathrm{NC}^{i} \subsetneq \mathrm{monotone}\text{-}\mathrm{NC}^{i+1}$, and $\mathrm{monotone}\text{-}\mathrm{NC} \subsetneq \mathrm{monotone}\text{-}\mathrm{P}$. More precisely, the monotone circuit depth of the generation problem $\mathrm{GEN}$ (given a set of triples defining a closure operation on $[n]$, decide whether $n$ is generated from $1$) is $n^{\Omega(1)}$, while $\mathrm{GEN}$ has polynomial-size monotone circuits.

## Proof sketch

By the monotone Karchmer-Wigderson theorem, monotone depth equals the communication complexity of the monotone KW game, which for $\mathrm{GEN}$ and related functions contains a lifted pebbling search problem. The Raz-McKenzie deterministic lifting theorem converts the decision-tree depth of the corresponding pyramid-pebbling search problem, which is polynomial, into an equal communication lower bound with the index gadget.

## Depends on

- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Proof depends on

- [Monotone circuits are rectangle-DAGs for monotone Karchmer–Wigderson games](../../communication-complexity/randomized-and-dag-like-lifting/monotone-circuit-rectangle-dag.md)
- [Composed functions, gadgets and lifting theorems](../../communication-complexity/randomized-and-dag-like-lifting/composed-function-lifting.md)

## Sources

- R. Raz, P. McKenzie, "Separation of the monotone NC hierarchy", Combinatorica 19 (1999) 403-435; FOCS (1997).
- M. Karchmer, A. Wigderson, "Monotone circuits for connectivity require super-logarithmic depth", SIAM Journal on Discrete Mathematics 3 (1990) 255-265.
