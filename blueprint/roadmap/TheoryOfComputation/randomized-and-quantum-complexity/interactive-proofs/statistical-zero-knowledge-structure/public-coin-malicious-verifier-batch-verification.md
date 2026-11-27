# Kaslasi–Rothblum–Vasudevan: public-coin malicious-verifier SZK batch verification for NISZK

If $\Pi$ has a non-interactive statistical zero-knowledge proof with communication $m$, then $\Pi^{\otimes k}$ has a public-coin statistical zero-knowledge proof that is zero knowledge against arbitrary (malicious) polynomial-time verifiers, with communication complexity

$$
\bigl(k+\mathrm{poly}(m)\bigr)\cdot\mathrm{polylog}(k,m).
$$

This removes both drawbacks (private coins and honest-verifier zero knowledge) of the earlier batch verification protocol for $\mathsf{NISZK}$ while keeping communication additive in $k$; the generic Goldreich–Sahai–Vadhan compiler from honest-verifier to malicious-verifier SZK would instead incur a polynomial overhead.

## Proof sketch

The protocol keeps the sequential structure over approximate-injectivity instances but replaces the verifier's private hashing challenges by public coins, using a carefully designed sampling step in which the prover proves that a hashed value has a preimage without the verifier needing hidden randomness. Malicious-verifier zero knowledge is obtained because every verifier message is a random string whose effect the simulator can reproduce by sampling preimages first and then defining the coins consistently.

## Depends on

- [Kaslasi–Rothblum–Rothblum–Sealfon–Vasudevan: HVSZK batch verification for NISZK with communication poly(n) + k·poly(log n, log k)](batch-verification-hvszk-for-niszk.md)
- [Public-coin interactive proofs](../../goldwasser-sipser-theorem/pub-ip.md)
- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)
- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)

## Proof depends on

- [Goldreich–Sahai–Vadhan: honest-verifier SZK equals general SZK](honest-verifier-szk-equals-general-szk.md)

## Sources

- Inbar Kaslasi, Ron D. Rothblum and Prashant Nalini Vasudevan, "Public-Coin Statistical Zero-Knowledge Batch Verification against Malicious Verifiers", EUROCRYPT (2021), ECCC TR21-029.
