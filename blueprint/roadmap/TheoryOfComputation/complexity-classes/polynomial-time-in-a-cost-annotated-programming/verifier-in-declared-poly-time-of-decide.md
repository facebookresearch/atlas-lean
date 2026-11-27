# A decider with polynomial declared time gives a verifier with polynomial declared time

If a timed decider $f$ on bit strings has declared time bounded by a polynomial in the input
length, then the verifier that sends an input $x$ and a witness $w$ to $f(x)$, ignoring $w$, has
declared time bounded by a polynomial in $|x| + |w|$.
