# INDEPENDENT-SET is verified with witnesses no longer than the input

For every bit string
$x$, $x$ is in INDEPENDENT-SET if and only if there is a bit string $w$ of length at most the
length of $x$ such that the shared CLIQUE / INDEPENDENT-SET / VERTEX-COVER verifier, run in
independent-set mode, accepts the input $x$ with witness $w$.
