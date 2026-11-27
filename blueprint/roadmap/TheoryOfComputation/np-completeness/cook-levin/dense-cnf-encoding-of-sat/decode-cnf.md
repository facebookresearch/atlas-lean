# Dense decoding of CNF formulas

The CNF formula decoded from a bit string $w$ is the
result of the accumulator decoding of $w$ started with no slots read for the current clause:
$w$ is read two bits at a time, $00$ ends a clause, $01$ is an empty slot, $10$ a positive and
$11$ a negative literal, and a trailing unterminated clause and a dangling odd bit are ignored.
