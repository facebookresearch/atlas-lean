# SAT WITH AT MOST THREE LITERALS PER CLAUSE AND AT MOST THREE CLAUSES PER VARIABLE as a decision problem

The decision problem SAT WITH AT MOST THREE LITERALS PER CLAUSE AND AT MOST THREE CLAUSES PER VARIABLE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a variable count and a CNF formula, to an instance that is [well-formed](well-formed-2-7.md) for it and whose formula has a satisfying assignment of $n$ truth values. It rejects every bitstring that does not decode to such an instance.
