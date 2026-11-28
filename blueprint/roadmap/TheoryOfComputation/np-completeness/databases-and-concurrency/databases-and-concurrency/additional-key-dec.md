# ADDITIONAL KEY as a decision problem

The decision problem ADDITIONAL KEY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples $(n, F, R, K)$, to an instance that is both

- [well-formed](well-formed.md): every name in every dependency of $F$, in $R$ and in every member of $K$ is below $n$, and every member of $K$, read as a set of attributes, is a key for $\langle R, F \rangle$ (a subset of $R$ from which $R$ follows by Armstrong's axioms, minimal under inclusion with this property);
- [feasible](additional-key-feasible.md): some key for $\langle R, F \rangle$ is, as a set of attributes, different from every member of $K$.

It rejects every bitstring that does not decode, or decodes to an instance with a name $n$ or larger in some list or with a member of $K$ that is not a key. Feasibility on its own reads the lists as sets of attributes, so the out-of-range rejection comes only from the well-formedness test.
