# The toric code encodes two qubits

For $L \ge 2$, the check operators of the [toric code](toric-code.md) generate a stabilizer group whose only relations
among the generators are $\prod_s A_s = I$ and $\prod_p B_p = I$: any $L^2 - 1$ of the vertex operators together with any
$L^2 - 1$ of the face operators are $2L^2 - 2$ independent generators. Hence the toric code has dimension
$2^{2L^2 - (2L^2 - 2)} = 4$: it encodes two qubits.

Proof: a product $\prod_{s \in V'} A_s$ is the identity only if every edge meets $V'$ in an even number of endpoints;
since the lattice is connected this forces $V' = \emptyset$ or all vertices. The same argument on the dual lattice
applies to faces, and products of $X$'s and of $Z$'s are independent of each other. The
[dimension formula](../stabilizer-codes/finrank-stabilizer-code.md) then gives $4$.

## Depends on

- [Toric code](toric-code.md)
- [Dimension of a stabilizer code](../stabilizer-codes/finrank-stabilizer-code.md)

## Proof depends on

- [The toric code check operators commute](toric-code-check-operators-commute.md)
- [Dimension of a stabilizer code](../stabilizer-codes/finrank-stabilizer-code.md)

## Sources

- A. Yu. Kitaev, *Fault-tolerant quantum computation by anyons*, Ann. Physics 303 (2003), 2–30, arXiv:quant-ph/9707021, Section 2 of the published article (Section 1 of the arXiv version) ("there are $m = 2k^2 - 2$ independent stabilizer operators ... $\dim L = 2^{n-m} = 4$").
- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.A.
