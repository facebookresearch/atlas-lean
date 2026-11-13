# The SAT verifier has polynomial declared time

There is a polynomial $q$ with natural
number coefficients such that for all lists of Booleans $x$ (the input) and $w$ (the witness),
the declared time cost of the SAT verifier on $(x, w)$ is at most $q(|x| + |w|)$.

One can take $q = X^2 + X$. This bounds only the trusted cost annotation.
