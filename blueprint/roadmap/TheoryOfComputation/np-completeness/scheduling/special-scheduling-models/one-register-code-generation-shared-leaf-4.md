# CODE GENERATION ON A ONE-REGISTER MACHINE (shared vertices have arcs only to leaves) is NP-complete

CODE GENERATION ON A ONE-REGISTER MACHINE (shared vertices have arcs only to leaves) is NP-complete: the decision problem over bitstrings that accepts exactly the bitstrings that decode to a well-formed instance with a solution lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The machine is the one of Garey and Johnson (1979), [PO4]: an operation at a vertex with two operands may take either of them from the register, the other from memory. Garey and Johnson credit the restriction to shared vertices with arcs only to leaves to Aho, Johnson and Ullman (1977), whose machine takes the operands of an operation in a fixed order; #10191 tracks the hardness argument for the either-operand model.

## Sources

- Garey and Johnson (1979), [PO4]; Aho, Johnson and Ullman (1977).
