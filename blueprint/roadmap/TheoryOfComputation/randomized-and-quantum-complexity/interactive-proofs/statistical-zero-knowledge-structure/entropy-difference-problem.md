# The Entropy Difference problem ED

For a circuit $C:\{0,1\}^m\to\{0,1\}^{n}$ let $H(C)$ denote the Shannon entropy of $C(U_m)$, the output distribution on a uniformly random input. **Entropy Difference** is the promise problem $\mathrm{ED}=(\mathrm{ED}_{\mathrm{yes}},\mathrm{ED}_{\mathrm{no}})$ on pairs of circuits:

$$
\mathrm{ED}_{\mathrm{yes}}=\{(X,Y):H(X)\ge H(Y)+1\},\qquad \mathrm{ED}_{\mathrm{no}}=\{(X,Y):H(Y)\ge H(X)+1\}.
$$

Swapping the two circuits maps $\mathrm{ED}_{\mathrm{yes}}$ onto $\mathrm{ED}_{\mathrm{no}}$ and vice versa, so $\mathrm{ED}$ is Karp-reducible to its own complement. The related one-sided problem **Entropy Approximation** $\mathrm{EA}$ takes a circuit $X$ and a threshold $k$ and asks whether $H(X)\ge k+1$ or $H(X)\le k-1$.

## Depends on

- [Shannon entropy](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Promise-SZK and HVSZK: statistical zero-knowledge proofs for promise problems](promise-szk-and-hvszk.md)

## Sources

- Oded Goldreich and Salil Vadhan, "Comparing Entropies in Statistical Zero Knowledge with Applications to the Structure of SZK", CCC (1999), ECCC TR98-063.
- Oded Goldreich, Amit Sahai and Salil Vadhan, "Can Statistical Zero Knowledge be made Non-Interactive? or On the Relationship of SZK and NISZK", CRYPTO (1999), ECCC TR99-013.
