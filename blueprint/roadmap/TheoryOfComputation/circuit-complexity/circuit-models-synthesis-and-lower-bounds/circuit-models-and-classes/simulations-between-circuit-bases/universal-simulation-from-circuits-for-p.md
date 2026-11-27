# Universal circuit simulation from circuits for P

Let $\Omega$ be a Boolean basis containing the unbounded fan-in basis. Suppose every language in $\mathsf{P}$ has circuits over $\Omega$ of size $t(n)$ and depth $d(n)$. Then every De Morgan circuit $C$ of size $T$ on $n$ inputs has an equivalent circuit over $\Omega$ of size $t\bigl(n+O((T+1)\log(n+T+2))\bigr)$ and the corresponding depth, obtained by hard-wiring the encoding of $C$ into the circuit for the circuit-evaluation language at that input length.

## Proof sketch

The language of pairs (encoded circuit, input) accepted by the circuit is in $\mathsf{P}$; the encoding of a size-$T$ circuit has length $O((T+1)\log(n+T+2))$, and fixing that prefix as constants leaves a circuit in the input $x$ alone.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [The complexity class P](../../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [The Circuit Value Problem is P-complete](../../../../completeness-other-classes/circuit-value-problem/cvp-p-complete.md)

## Sources

- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2, 2014.
