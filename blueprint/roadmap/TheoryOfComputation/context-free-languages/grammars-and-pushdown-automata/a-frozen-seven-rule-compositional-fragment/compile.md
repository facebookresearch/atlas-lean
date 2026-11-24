# Compile

Compile a valid derivation tree to the intrinsic term at its root
category's semantic type, by structural recursion on the tree, using
exactly the seven actions above. Invalid trees have no validity
witness, so no default term is returned for an invalid rule. Proof
arguments do not affect the output (`compile_proof_irrel`).
