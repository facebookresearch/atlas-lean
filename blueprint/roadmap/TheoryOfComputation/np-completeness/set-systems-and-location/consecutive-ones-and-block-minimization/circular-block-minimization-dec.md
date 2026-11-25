# CIRCULAR BLOCK MINIMIZATION as a decision problem

The decision problem CIRCULAR BLOCK MINIMIZATION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, A, K)$ (a natural number, a list of lists of booleans and a natural number), to an instance that is well-formed for CONSECUTIVE BLOCK MINIMIZATION (every row of $A$ has exactly $n$ entries and $K > 0$) and feasible for CIRCULAR BLOCK MINIMIZATION. It rejects every bitstring that does not decode to such an instance.
