# Witnesses that do not decode are rejected

If the witness decoder fails on a bit string
$w$, then for every bit string $x$ the HAMPATH verifier rejects $(x, w)$, that is, returns false.
