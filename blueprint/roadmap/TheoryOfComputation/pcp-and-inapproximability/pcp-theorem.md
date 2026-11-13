# The PCP theorem: NP = PCP(O(log n), O(1))

A decision problem belongs to NP if and only
if, for some natural numbers $c$ and $q$, it belongs to $\mathrm{PCP}(r, s)$, where the
randomness bound is $r(n) = c \lfloor \log_2(n + 1) \rfloor$ and the query bound is the constant
function $s(n) = q$.

## Sources

- S. Arora, C. Lund, R. Motwani, M. Sudan, and M. Szegedy, "Proof verification and the hardness of approximation problems", Journal of the ACM 45 (1998), 501-555 (FOCS 1992); S. Arora and S. Safra, "Probabilistic checking of proofs: a new characterization of NP", Journal of the ACM 45 (1998), 70-122.
