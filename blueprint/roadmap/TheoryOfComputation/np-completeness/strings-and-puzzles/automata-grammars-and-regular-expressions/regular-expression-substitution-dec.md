# REGULAR EXPRESSION SUBSTITUTION as a decision problem

The decision problem REGULAR EXPRESSION SUBSTITUTION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples (an alphabet size, a token list, a list of token lists and a string), to an instance that is [well-formed](well-formed-2-7.md) and [feasible](regular-expression-substitution-feasible.md) for REGULAR EXPRESSION SUBSTITUTION. It rejects every bitstring that does not decode to such an instance.
