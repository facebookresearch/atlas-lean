# MCSP is in NP

MCSP is in NP: on input $(T, s)$ with $|T| = 2^n$, a certificate is a circuit of size at most $s$ (which can be assumed to have size at most the input length, since every function has circuits of size $O(2^n/n)$), and the verifier evaluates it on all $2^n$ inputs in time polynomial in $|T|$.

## Proof sketch

Encode circuits of size $s$ with $O(s \log s)$ bits; thresholds above the Shannon–Lupanov bound make every truth table a yes-instance, so the certificate length can be capped by a polynomial in $2^n$.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](minimum-circuit-size-problem.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [The Shannon–Lupanov window for MCSP](shannon-lupanov-window-for-mcsp.md)

## Sources

- V. Kabanets and J.-Y. Cai, "Circuit Minimization Problem", STOC 2000.
