# Three-valued evaluation of unbounded fan-in circuits under restrictions

Read $\{0,1,\ast\}$ as Kleene's strong three-valued logic ($\ast$ = unknown): a conjunction is $0$ as soon as one argument is $0$, $1$ if all are $1$, and $\ast$ otherwise; dually for disjunction; $\neg\ast=\ast$. For every circuit $C$ over NOT and unbounded fan-in AND and OR gates (the unbounded fan-in basis without MOD gates) and every restriction (partial assignment) $\rho$, evaluating $C$ on $\rho$ (unfixed inputs set to $\ast$) is monotone with respect to refinement, and if it yields $b\in\{0,1\}$ then $C|_\rho$ is the constant function $b$.

## Proof sketch

Induction on gates: Kleene's connectives are monotone in the information order and agree with Boolean connectives on total inputs.

## Depends on

- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Sources

- Stephen Cole Kleene, "Introduction to Metamathematics", North-Holland and Van Nostrand, 1952.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
