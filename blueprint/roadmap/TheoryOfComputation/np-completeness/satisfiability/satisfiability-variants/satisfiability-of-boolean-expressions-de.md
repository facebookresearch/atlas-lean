# SATISFIABILITY OF BOOLEAN EXPRESSIONS as a decision problem

The decision problem SATISFIABILITY OF BOOLEAN EXPRESSIONS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples (a variable count, a list of connective codes and a postfix token list), to an instance that is [well-formed](well-formed-2-6.md) and [feasible](satisfiability-of-boolean-expressions-fe.md) for SATISFIABILITY OF BOOLEAN EXPRESSIONS. It rejects every bitstring that does not decode to such an instance.
