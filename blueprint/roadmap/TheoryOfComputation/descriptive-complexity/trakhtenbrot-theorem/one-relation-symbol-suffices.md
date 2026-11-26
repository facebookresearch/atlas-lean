# One relation symbol suffices for finite satisfiability

There is a computable map sending every relational first-order sentence $\varphi$ to a sentence $\varphi'$ that uses a single relation symbol $R$ (at several positive arities, or at one arity after padding) such that $\varphi$ is finitely satisfiable iff $\varphi'$ is. Moreover any sentence over one relation symbol of arity $l \ge 2$ can be translated, preserving finite satisfiability, into a sentence over a single binary relation $E$, by interpreting tuples through gadget vertices: the domain is the set of loops $E(x,x)$ and each atom becomes a tuple-gadget formula.

## Proof sketch

Replace each atom $R_r(\bar x)$ by $R(\bar x, x_B, \dots, x_B)$ padded to a length coding the pair $(r, |\bar x|)$ injectively. For the binary step use a relativized interpretation whose non-loop gadget vertices encode tuples, so models correspond in both directions.

## Depends on

- [Finite satisfiability and finite validity](finite-satisfiability-and-validity.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
