# Axiomatizing arithmetic on finite initial segments

There is a finite set of first-order sentences over relation symbols $<$ (binary), $Z$ (unary), $S$ (binary) and $P$ (ternary) whose finite models are, up to isomorphism, exactly the structures on initial segments $\{0,\dots,N-1\}$ with the standard strict order, $Z = \{0\}$, $S$ the graph of $a \mapsto a + 1$ restricted to the segment, and $P$ a relation contained in the graph of a fixed injective pairing function $\langle a, b \rangle$ that is total on all pairs whose code lies in the segment. Since functions are not total on a finite segment, they are axiomatized as relations.

## Proof sketch

A strict linear order with least element and successor relation on a finite set is isomorphic to an initial segment of $\mathbb{N}$; the pairing axioms recursively pin down $P$ on its domain.

## Depends on

- [Finite satisfiability and finite validity](finite-satisfiability-and-validity.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- B. A. Trakhtenbrot, "Impossibility of an Algorithm for the Decision Problem in Finite Classes", Doklady Akademii Nauk SSSR 70, 569–572, 1950.
