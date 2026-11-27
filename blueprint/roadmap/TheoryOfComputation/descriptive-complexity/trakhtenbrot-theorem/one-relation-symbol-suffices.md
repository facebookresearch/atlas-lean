# One relation symbol suffices for finite satisfiability

There is a computable map sending every first-order sentence $\varphi$ over a finite relational vocabulary with $s$ symbols of maximal arity $m$ to a sentence $\varphi'$ over a single relation symbol $R$ of arity $m + s$ such that $\varphi$ is finitely satisfiable iff $\varphi'$ is. Moreover any sentence over one relation symbol of arity $l \ge 2$ can be translated, preserving finite satisfiability, into a sentence over a single binary relation $E$, by interpreting tuples through gadget vertices: the domain is the set of loops $E(x,x)$ and each atom becomes a tuple-gadget formula.

## Proof sketch

If $\varphi$ has a one-element model (a decidable condition) output a fixed finitely satisfiable sentence; otherwise let $\varphi' = \exists u \exists v\,(u \ne v \wedge \varphi^*)$, where $\varphi^*$ replaces the atom $R_i(\bar x)$ by $R(\bar x, u, \dots, u, \bar t_i)$, padded with $u$ to $m$ arguments and tagged by $\bar t_i \in \{u,v\}^s$ with $u$ exactly in place $i$. For the binary step use a relativized interpretation whose non-loop gadget vertices encode tuples, so models correspond in both directions.

## Depends on

- [Finite satisfiability and finite validity](finite-satisfiability-and-validity.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
