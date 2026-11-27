# Instances that do not decode are rejected

If the PATH instance decoder fails on a bit
string $x$, then for every bit string $w$ the HAMPATH verifier rejects $(x, w)$, that is, returns
false.
