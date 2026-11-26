# EDOL GRAMMAR NON-EMPTINESS as a decision problem

The decision problem EDOL GRAMMAR NON-EMPTINESS accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of quadruples $(n, k, \delta, S)$ of nonterminal and terminal counts, a list of tables and an initial nonterminal, to an instance that is [well-formed](well-formed.md) and [feasible](edolgrammar-non-emptiness-feasible.md) for EDOL GRAMMAR NON-EMPTINESS. It rejects every bitstring that does not decode to such an instance.
