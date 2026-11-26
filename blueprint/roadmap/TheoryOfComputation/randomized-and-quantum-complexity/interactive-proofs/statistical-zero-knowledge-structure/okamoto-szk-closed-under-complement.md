# Okamoto: SZK is closed under complement

For every promise problem $\Pi=(\Pi_{\mathrm{yes}},\Pi_{\mathrm{no}})$, if $\Pi\in\mathsf{HVSZK}$ then $\overline\Pi=(\Pi_{\mathrm{no}},\Pi_{\mathrm{yes}})\in\mathsf{HVSZK}$; the same holds for $\mathsf{SZK}$. Thus every problem with statistical zero-knowledge proofs of membership also has statistical zero-knowledge proofs of non-membership, in sharp contrast with the situation expected for $\mathsf{NP}$ versus $\mathsf{coNP}$.

## Proof sketch

Compose the Karp reduction from $\Pi$ to $\mathrm{ED}$ with the swap map $(X,Y)\mapsto(Y,X)$, which reduces $\mathrm{ED}$ to its complement; this reduces $\overline\Pi$ to $\mathrm{ED}$, which is in $\mathsf{HVSZK}$. The statement for $\mathsf{SZK}$ follows from $\mathsf{HVSZK}=\mathsf{SZK}$.

## Depends on

- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)

## Proof depends on

- [The Entropy Difference problem ED](entropy-difference-problem.md)
- [Goldreich–Vadhan: every HVSZK problem Karp-reduces to Entropy Difference](every-hvszk-problem-reduces-to-ed.md)
- [Goldreich–Vadhan: Entropy Difference has a public-coin honest-verifier statistical zero-knowledge proof](entropy-difference-has-public-coin-hvszk-proof.md)

## Sources

- Tatsuaki Okamoto, "On Relationships between Statistical Zero-Knowledge Proofs", Journal of Computer and System Sciences 60(1) (2000).
- Oded Goldreich and Salil Vadhan, "Comparing Entropies in Statistical Zero Knowledge with Applications to the Structure of SZK", CCC (1999), ECCC TR98-063.
- Amit Sahai and Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2) (2003), ECCC TR00-084.
