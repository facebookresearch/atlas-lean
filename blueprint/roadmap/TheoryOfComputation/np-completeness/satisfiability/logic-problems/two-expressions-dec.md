# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES FOR TWO DISTINCT ENCODINGS as a decision problem

The decision problem TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES FOR TWO DISTINCT ENCODINGS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a variable count and a list of postfix expressions, to an instance that is [well-formed](well-formed-2-6.md) for it, so a list of two encodings that differ as token lists, and feasible for TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES. It rejects every bitstring that does not decode to such an instance.

This is not the restriction of TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES to two distinct expressions: it also accepts two different encodings of one complete expression, such as NAND.
