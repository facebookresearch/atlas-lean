# Dense decoding with an accumulator

Given a bit string $w$ and the list $c$ of slots read so
far for the current clause, stored in reverse order, the result is the CNF formula obtained by
reading $w$ two bits at a time: $00$ outputs the current clause in reading order and continues
with no slots read; $01$ adds an empty slot to the current clause; and $1s$, for a bit $s$, adds a
slot holding the Boolean $\lnot s$, so $10$ adds a positive and $11$ a negative literal. When
fewer than two bits remain, decoding stops and outputs no further clauses, so a trailing
unterminated clause and a dangling odd bit are ignored and decoding is total.
