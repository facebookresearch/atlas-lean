# Kaslasi–Rothblum–Rothblum–Sealfon–Vasudevan: HVSZK batch verification for NISZK with communication poly(n) + k·poly(log n, log k)

For a promise problem $\Pi$ let $\Pi^{\otimes k}$ have YES instances $(x_1,\dots,x_k)$ with all $x_i\in\Pi_{\mathrm{yes}}$ and NO instances with every $x_i\in\Pi_{\mathrm{yes}}\cup\Pi_{\mathrm{no}}$ and at least one $x_i\in\Pi_{\mathrm{no}}$, all of length $n$. If $\Pi\in\mathsf{NISZK}$, then for every $k=k(n)$ there is an interactive honest-verifier statistical zero-knowledge protocol for $\Pi^{\otimes k}$ with communication complexity

$$
\mathrm{poly}(n)+k\cdot\mathrm{poly}(\log n,\log k),
$$

where the polynomials are fixed, depending only on $\Pi$ and not on $k$; the verifier runs in time $k\cdot\mathrm{poly}(n)$ and the protocol has $O(k)$ rounds. The naive approach of running $k$ independent proofs costs $k\cdot\mathrm{poly}(n)$ communication.

## Proof sketch

Reduce each $x_i$ to an instance $C_i$ of $\mathrm{AI}_\delta$. For permutations, $k$ instances could be batched by composing them, since $C_k\circ\cdots\circ C_1$ is a permutation iff each is; for almost-injective circuits the protocol instead walks through the instances sequentially, at each step having the prover reveal a preimage of a hashed value whose description is short, so that each additional instance costs only $\mathrm{poly}(\log n,\log k)$ bits. Near-injectivity of YES instances keeps the walk on a unique path that the honest-verifier simulator can sample forwards, and a collision in any NO instance makes the prover's answer wrong with constant probability.

## Depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)
- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)

## Proof depends on

- [Kaslasi et al.: Approximate Injectivity is NISZK-complete](approximate-injectivity-niszk-complete.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Inbar Kaslasi, Guy N. Rothblum, Ron D. Rothblum, Adam Sealfon and Prashant Nalini Vasudevan, "Batch Verification for Statistical Zero Knowledge Proofs", TCC (2020), ECCC TR20-147.
