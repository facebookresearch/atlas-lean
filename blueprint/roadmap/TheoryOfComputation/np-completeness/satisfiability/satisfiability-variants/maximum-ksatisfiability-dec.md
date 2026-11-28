# MAXIMUM k-SATISFIABILITY as a decision problem

Fix a natural number $k$. The decision problem MAXIMUM k-SATISFIABILITY accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of MAXIMUM SATISFIABILITY instances, to an instance that is [well-formed](well-formed-2-4.md) for clause width $k$ and feasible for MAXIMUM SATISFIABILITY. It rejects every bitstring that does not decode to such an instance.
