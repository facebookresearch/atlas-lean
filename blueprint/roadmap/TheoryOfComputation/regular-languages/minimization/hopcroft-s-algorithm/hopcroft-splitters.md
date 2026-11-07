# Trace of splitters popped by Hopcroft's algorithm

The splitters popped by Hopcroft's loop, in order: the same recursion as
`DFA.hopcroftLoop`, collecting each popped splitter. The cost of processing one popped
splitter `(C, a)` is `(preimage M C a).card + 1`: one predecessor visit per state whose
`a`-successor lies in `C`, plus `O(1)` per-splitter overhead. See `hopcroftCost`.
`hopcroftLoop_eq_hopcroftLoop_of_length` proves this trace records exactly the
splitters the loop pops, so the trace cannot drift from the loop.
