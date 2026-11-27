# Baur–Strassen: all partial derivatives at constant-factor cost

Let $f\in K[x_1,\dots,x_n]$ be computed by an arithmetic circuit with $s$ gates (additions, multiplications, constants). Then there is an arithmetic circuit with at most $5s+O(1)$ gates computing $f$ together with all its partial derivatives $\partial f/\partial x_1,\dots,\partial f/\partial x_n$, and its multiplicative cost is at most three times that of the original. Consequently a lower bound $L$ for computing all partial derivatives of $f$ implies $L(f)\ge L/5-O(1)$; with Strassen's degree bound for $x_1^{d-1},\dots,x_n^{d-1}$ this gives $L\bigl(\sum_ix_i^{d}\bigr)\ge\tfrac15\,n\log_2(d-1)-O(1)$ for $d\ge2$ over every infinite field whose characteristic does not divide $d$ (the partial derivatives are $d\,x_i^{d-1}$, and $d$ is invertible).

## Proof sketch

Reverse-mode differentiation: run the circuit forward, then traverse the gates backwards maintaining for every wire an adjoint (the derivative of the output with respect to that wire); an addition propagates its adjoint to both arguments, a multiplication $w=uv$ adds $\bar w v$ to $\bar u$ and $\bar w u$ to $\bar v$. Each gate contributes a constant number of operations.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Walter Baur, Volker Strassen, "The Complexity of Partial Derivatives", Theoretical Computer Science, 1983.
- Jacques Morgenstern, "How to Compute Fast a Function and All Its Derivatives: A Variation on the Theorem of Baur–Strassen", ACM SIGACT News, 1985.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
