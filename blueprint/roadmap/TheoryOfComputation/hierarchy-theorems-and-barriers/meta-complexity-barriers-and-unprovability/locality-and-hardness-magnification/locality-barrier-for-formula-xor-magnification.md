# Locality barrier for the Formula-XOR magnification frontier

The Formula-XOR magnification theorem for MCSP unconditionally yields Formula-XOR circuits of size $N^{1.01}$ with small fan-in oracle gates, while the known inner-product lower bound for Formula-XOR still holds in the presence of such oracles. Hence that lower bound technique cannot prove the lower bound the magnification theorem needs.

Let $N = 2^n$. The following hold.

1. For every $\varepsilon > 0$, $\mathrm{MCSP}[2^{n^{1/3}}, 2^{n^{2/3}}] \in \mathsf{Formula}\text{-}\mathcal{O}\text{-}\mathsf{XOR}[N^{1.01}]$ for some oracle $\mathcal{O}$, where every oracle gate has fan-in at most $N^{\varepsilon}$ and appears in the layer right above the XOR leaves.
2. For every $\delta > 0$ and every oracle $\mathcal{O}$, $\mathsf{InnerProduct}$ on $N$ input bits cannot be computed by $\mathsf{Formula}\text{-}\mathcal{O}\text{-}\mathsf{XOR}$ circuits of size $N^{2 - 3\delta}$ with at most $N^{2-3\delta}$ oracle gates of fan-in $N^{\delta}$ in the layer right above the XOR leaves.
3. There is a universal constant $c$ such that for all constants $\varepsilon > 0$ and $\alpha > 2$, $\mathrm{MCSP}[n^c, 2^{(\varepsilon/\alpha) n}]$ cannot be computed by oracle formulas $F$ with $\mathrm{Size}_3(F) \le N^{2 - \varepsilon}$ and adaptivity $o(\log N / \log\log N)$, where $\mathrm{Size}_t(F)$ is the size of the formula obtained by replacing every oracle gate of fan-in $\beta$ by a formula of size $\beta^t$ reading each input $\beta^{t-1}$ times.

In contrast, the magnification theorem states that $\mathrm{MCSP}[2^{n^{1/3}}, 2^{n^{2/3}}] \notin \mathsf{Formula}\text{-}\mathsf{XOR}[N^{1.01}]$ implies $\mathsf{NQP} \not\subseteq \mathsf{NC}^1$.

## Expansion

Item 1 is read off the magnification proof: it reduces an MCSP instance by parities to queries of length $N^{\varepsilon}$ to a fixed language and only afterwards uses a complexity collapse to replace the queries by small formulas; stopping before that step gives the oracle circuit unconditionally. Item 2 localizes Tal's argument: replacing each oracle gate by a new variable, a De Morgan formula of size $t$ is approximated by a real polynomial of degree $O(\sqrt{t})$, and expanding each oracle into its Fourier expansion over its $N^{\delta}$ parity inputs gives a sign representation with $s^{O(\sqrt{s})} 2^{N^{\delta} O(\sqrt{s})}$ monomials, below Forster's sign-rank bound $2^{N/2}$ for inner product. A reduction from inner product to this MCSP variant of the required form is therefore impossible as well.

## Depends on

- [Formula-XOR circuits and their local oracle extension](formula-xor-circuits.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Nondeterministic quasi-polynomial time](../../../circuit-complexity/algorithmic-method-nqp-and-almost-everywhere-bounds/nqp-class.md)

## Proof depends on

None.

## Sources

- Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Jan Pich, Ninad Rajgopal and Rahul Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", *Journal of the ACM* 69(4), 2022 (conference version ITCS 2020), DOI 10.1145/3538391, arXiv:1911.08297v1 (Theorem 2, Locality Barrier for HM Frontier B, Section 1.3; frontier B item B1 in Section 3.2; proofs in Section 5).
