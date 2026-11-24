# Verifiers with polynomial declared time

A timed verifier $V$, which assigns to each pair
of bit strings $(x, w)$ (an input and a witness) a timed computation returning a Boolean, runs in
declared polynomial time when there is a polynomial $q$ with natural coefficients such that the
declared time of $V(x, w)$ is at most $q(|x| + |w|)$ for all $x$ and $w$.

As for deciders, this constrains only the declared time, which is a trusted annotation, and
establishes no computability in any machine model.
