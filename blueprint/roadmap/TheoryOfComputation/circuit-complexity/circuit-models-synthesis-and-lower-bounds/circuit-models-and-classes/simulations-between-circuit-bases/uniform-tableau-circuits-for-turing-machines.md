# Uniform tableau circuits for multi-tape Turing machines

For every multi-tape Turing machine $M$ over $\{0,1\}$ and every time bound $T$, there is a De Morgan circuit $C_{n,T}$ with $n$ inputs and $O(T^2)$ gates (for a fixed machine) that computes the configuration of $M$ after $T$ steps on every input of length $n$, in particular its acceptance bit. The circuit is uniform in a strong sense: given $n,T$ and a gate number $g$ in binary, the type and the arguments of gate $g$ are computable in space linear in the length of $(n,T,g)$. Its Tseitin formula has clauses described by fixed symbolic shapes on bit-field labels, so it is a succinct CNF.

## Proof sketch

Lay out one block of wires per time step holding the basic features of the configuration (state, head contents, head movements) and copy cells that are not under a head; each cell at step $t+1$ depends on a constant number of cells at step $t$, so each step costs $O(T)$ gates. Gate numbers decompose into (step, cell, local gadget) fields, which yields the space-efficient gate description.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Deterministic time classes on multi-tape machines](../../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [P is contained in P/poly](../../../../complexity-classes/time-and-space-complexity-classes/p-is-contained-in-p-poly.md)
- [Tseitin encoding of a Boolean circuit](../circuit-models-and-complexity-measures/tseitin-encoding-of-a-circuit.md)

## Sources

- Richard E. Ladner, "The Circuit Value Problem Is Log Space Complete for P", ACM SIGACT News, 1975.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
- Ryan Williams, "Improving Exhaustive Search Implies Superpolynomial Lower Bounds", Author's full version, 2010.
