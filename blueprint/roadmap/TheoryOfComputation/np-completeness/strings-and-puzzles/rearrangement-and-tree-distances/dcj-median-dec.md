# DCJ MEDIAN as a decision problem

The decision problem DCJ MEDIAN accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quintuples (a unary gene count, three adjacency lists and a bound), to an instance that is [well-formed](well-formed-3.md) and [feasible](dcjmedian-feasible.md) for DCJ MEDIAN. It rejects every bitstring that does not decode to such an instance.
