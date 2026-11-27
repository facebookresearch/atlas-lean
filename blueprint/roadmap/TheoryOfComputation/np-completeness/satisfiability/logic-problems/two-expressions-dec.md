# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES FOR TWO DISTINCT EXPRESSIONS as a decision problem

The decision problem TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES FOR TWO DISTINCT EXPRESSIONS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a variable count and a list of postfix expressions, to an instance that is [well-formed](well-formed-2-6.md) for it, so a list of two token lists whose parsed expressions differ, and feasible for TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES. It rejects every bitstring that does not decode to such an instance.

This is the restriction of TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES to two distinct expressions: two different encodings of one expression, such as two spellings of NAND, form a malformed instance.
