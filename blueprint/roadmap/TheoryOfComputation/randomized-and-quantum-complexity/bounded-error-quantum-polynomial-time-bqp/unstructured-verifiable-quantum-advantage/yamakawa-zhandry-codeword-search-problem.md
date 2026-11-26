# The Yamakawa-Zhandry codeword search problem

Fix a linear code $C \subseteq \Sigma^n$ with $\Sigma = \mathbb{F}_q$ (in the construction a folded Reed-Solomon code over an extension alphabet) and independent random functions $H_1, \dots, H_n : \Sigma \to \{0,1\}$, accessible as an oracle $H(i, \sigma) = H_i(\sigma)$. The *codeword search problem* $\mathrm{YZ}^{H}_C$ asks to output $x = (x_1, \dots, x_n) \in C$ with $H_i(x_i) = 1$ for every $i \in [n]$. For a fixed codeword each coordinate condition holds independently with probability $1/2$, so $|C|$ alone only bounds the *expected* number of solutions, $|C|\,2^{-n}$; it does not give a solution with high probability. Even a large linear code may have every codeword equal to $0$ in coordinate $1$, and then with probability $1/2$ the oracle rejects that symbol and no codeword works. For the folded Reed–Solomon code and parameters specified by Yamakawa and Zhandry (Lemma 4.2), their quantum algorithm outputs a solution with overwhelming probability over $H$ and its own randomness (Lemma 6.3, correctness of the proof of quantumness), so for that code a solution exists with overwhelming probability.

## Depends on

- [Search problems relative to a random oracle](search-problems-relative-to-a-random-oracle.md)
- [Reed-Solomon code](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063 (Lemmas 4.2 and 6.3).
