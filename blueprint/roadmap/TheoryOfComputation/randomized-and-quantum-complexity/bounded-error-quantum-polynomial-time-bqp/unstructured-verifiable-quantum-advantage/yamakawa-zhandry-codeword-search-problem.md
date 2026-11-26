# The Yamakawa-Zhandry codeword search problem

Fix a linear code $C \subseteq \Sigma^n$ with $\Sigma = \mathbb{F}_q$ (in the construction a folded Reed-Solomon code over an extension alphabet) and independent random functions $H_1, \dots, H_n : \Sigma \to \{0,1\}$, accessible as an oracle $H(i, \sigma) = H_i(\sigma)$. The *codeword search problem* $\mathrm{YZ}^{H}_C$ asks to output $x = (x_1, \dots, x_n) \in C$ with $H_i(x_i) = 1$ for every $i \in [n]$. A solution exists with high probability whenever $|C| \gg 2^n$, since each coordinate condition holds independently with probability $1/2$ for a fixed codeword.

## Depends on

- [Search problems relative to a random oracle](search-problems-relative-to-a-random-oracle.md)
- [Reed-Solomon code](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
