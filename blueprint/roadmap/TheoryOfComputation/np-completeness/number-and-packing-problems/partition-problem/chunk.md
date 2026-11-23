# Output bits per input bit in the doubling pass

The output of the doubling pass for one input bit $b$ read in [phase](phase.md) $q$: in phase
start, a true bit (the first marker of a nonempty block) is output as the three bits true, false,
true, which insert the new lowest binary digit $0$ of the doubled number; in every other case the
output is the single bit $b$.
