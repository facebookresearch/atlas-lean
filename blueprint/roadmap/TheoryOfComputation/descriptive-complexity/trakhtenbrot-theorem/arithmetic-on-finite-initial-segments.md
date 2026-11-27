# Axiomatizing arithmetic on finite initial segments

There is a finite set of first-order sentences over relation symbols $<$ (binary), $Z$ (unary), $S$ (binary) and $P$ (ternary) whose finite models are, up to isomorphism, exactly the structures on initial segments $\{0,\dots,N-1\}$ with the standard strict order, $Z = \{0\}$, $S$ the graph of $a \mapsto a + 1$ restricted to the segment, and $P = \{(a,b,c) : c = \langle a,b\rangle < N\}$ for a fixed bijective pairing function $\langle\cdot,\cdot\rangle : \mathbb{N}^2 \to \mathbb{N}$ with $a, b \le \langle a, b\rangle$ (for instance Cantor's), so $P$ is the graph of the pairing function restricted to the pairs whose code lies in the segment. Since functions are not total on a finite segment, they are axiomatized as relations.

## Proof sketch

A strict linear order with least element and successor relation on a finite set is isomorphic to an initial segment of $\mathbb{N}$; the pairing axioms (the code of $(0,0)$ is $0$; the successor of the code of $(a+1,b)$ codes $(a,b+1)$ and that of $(0,b)$ codes $(b+1,0)$; $P$ is functional and injective; every element is a code) pin down $P$ by induction along $S$.

## Depends on

- [Finite satisfiability and finite validity](finite-satisfiability-and-validity.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- B. A. Trakhtenbrot, "Impossibility of an Algorithm for the Decision Problem in Finite Classes", Doklady Akademii Nauk SSSR 70, 569–572, 1950.
