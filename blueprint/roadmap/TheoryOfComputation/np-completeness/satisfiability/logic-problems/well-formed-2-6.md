# Well-formed instances of TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES FOR TWO DISTINCT EXPRESSIONS

An instance is well-formed when every member of $C$ is the postfix token encoding of an expression over $u_0, \dots, u_{n-1}$, and $C$ is a list of exactly two token lists whose parsed expressions differ. Distinct token lists are not enough: the reader ignores the second component of operator tokens, so two token lists for the same NAND expression that differ only in the token used for a negation are one expression, and such a pair is malformed.
