# Soundness of one sum-check round

Over a finite field, let $p$ be a polynomial of degree at most $d$ and suppose the claimed sum is false, $H \ne p(0) + p(1)$. For every prover polynomial $q$, the number of challenges $r$ at which the verifier accepts, namely $\deg q \le d$, $q(0) + q(1) = H$ and $q(r) = p(r)$, is at most $d$.
