# Huang–Ilango–Ren: witness encryption gives near-optimal NP-hardness of approximating K^t(x|y) for t ≫ |y|; MOCSP is unconditionally NP-hard to approximate

1. **Conditional.** If subexponentially secure witness encryption exists, then the following promise problem is $\mathsf{NP}$-hard under randomized polynomial-time many-one (black-box) reductions: given $(x,y)$ with $|x|=n$ and $|y|=\mathrm{poly}(n)$, accept if $K^{\mathrm{poly}(n)}(x\mid y)\le n^{0.01}$ and reject if $K^{2^{n}}(x\mid y)\ge n-O(1)$. The constant $0.01$ can be any positive constant and the exponent $n$ in the NO time bound can be any polynomial in $n$; this is the superlinear regime $t\gg|y|$, whereas earlier hardness of approximation ($n^{1/\mathrm{poly}(\log\log n)}$ factors) was only for $t\ll|y|$. Assuming in addition subexponentially secure injective one-way functions, the additive-gap problem whose $\mathsf{NP}$-hardness Hirahara showed would exclude Heuristica is $\mathsf{NP}$-hard.
2. **Unconditional.** For every $\epsilon>0$ it is $\mathsf{NP}$-hard under randomized polynomial-time mapping reductions to distinguish, given a truth table $f$ of length $\ell$ and an oracle truth table $O$ of length $\mathrm{poly}(\ell)$, between $\mathrm{CC}^{O}(f)\le\ell^{\epsilon}$ and $\mathrm{CC}^{O}(f)\ge\ell^{1-\epsilon}$, where $\mathrm{CC}^{O}$ is minimum $O$-oracle circuit size (the Minimum Oracle Circuit Size Problem, MOCSP); in the full version the NO case is strengthened to average-case oracle circuit complexity at least $2^{(1-\epsilon)n}$ with YES complexity at most $2^{\epsilon n}$.

## Proof sketch

In item 1, a formula $\varphi$ is mapped to $x$ a random string and $y$ a list of witness encryptions, under $\varphi$, of the bits of $x$: if $\varphi$ is satisfiable, a short program containing a witness decrypts $y$ to $x$; if not, security of the encryption makes $y$ useless for describing $x$ even in exponential time, so $x$ keeps nearly full conditional complexity. In item 2, the same idea runs in an oracle world where witness encryption is provably secure: the Garg–Gentry–Sahai–Waters candidate is secure in the generic multilinear-map model, which can be implemented by the oracle truth table $O$, so no unproven assumption is needed.

## Depends on

- [Witness encryption for NP languages](../../../ComputerScience/cryptography/public-key/obfuscation-and-witness-encryption/witness-encryption-and-evasive-lwe/witness-encryption.md)
- [Distributional Kolmogorov complexity dK^t_λ(x|D) and its probabilistic variant](distributional-kolmogorov-complexity.md)

## Proof depends on

- [Few strings have small complexity](../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)

## Sources

- Yizhi Huang, Rahul Ilango and Hanlin Ren, "NP-Hardness of Approximating Meta-Complexity: A Cryptographic Approach", STOC (2023), ECCC TR23-046.
