# PARKS PUZZLE as a decision problem

Fix natural numbers $c$ and $r$. The decision problem PARKS PUZZLE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of boards given as lists of lists of natural numbers, to an instance that is well-formed and feasible for the $(c, r)$-tree puzzle. It rejects every bitstring that does not decode to such an instance.
