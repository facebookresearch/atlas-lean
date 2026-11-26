# The toric code has distance $L$

For $L \ge 2$ the [toric code](toric-code.md) on the $L \times L$ torus is a $[[2L^2, 2, L]]$ code. Hence it corrects
$\lfloor (L - 1)/2 \rfloor$ errors, a number growing with the lattice although each check operator acts on only four
qubits.

Proof: by the [characterisation of the logical operators](logical-operators-of-the-toric-code.md), a Pauli operator in
the normalizer but not in the stabilizer times phases has a $Z$ part that is a homologically nontrivial cycle of the
lattice or an $X$ part that is a nontrivial cycle of the dual lattice, and such a cycle winds around the torus and so has
at least $L$ edges; the straight loops have exactly $L$. The
[distance criterion for stabilizer codes](../stabilizer-codes-correctability-criterion-and-distance.md) gives distance $L$,
and the code has dimension $4$ by [the count of generators](toric-code-encodes-two-qubits.md).

## Depends on

- [Toric code](toric-code.md)
- [$[[n, k, d]]$ quantum code](../distance-of-a-quantum-code/n-k-d-quantum-code.md)

## Proof depends on

- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)
- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md)
- [The toric code encodes two qubits](toric-code-encodes-two-qubits.md)
- [Homologically nontrivial cycles on the $L \times L$ torus have length at least $L$](homologically-nontrivial-cycles-on-the-torus-have-length-at-least-l.md)
- [A code of distance $2t + 1$ corrects $t$ errors](../distance-of-a-quantum-code/is-correctable-of-has-distance-at-least.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.A ("in the case of an $L \times L$ square lattice drawn on the torus, the code distance is $d = L$").
- A. Yu. Kitaev, *Fault-tolerant quantum computation by anyons*, Ann. Physics 303 (2003), 2–30, arXiv:quant-ph/9707021, Section 2 of the published article (Section 1 of the arXiv version) (the code detects $k - 1$ errors).
