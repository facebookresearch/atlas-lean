# Symmetric alternation: the classes S2TIME[T], S2P and S2E

Let $T\colon\mathbb{N}\to\mathbb{N}$. A language $L$ is in $\mathrm{S}_2\mathrm{TIME}[T(n)]$ if there is an $O(T(n))$-time verifier $V(x,\pi_1,\pi_2)$, with $\pi_1,\pi_2\in\{0,1\}^{T(n)}$, such that

1. if $x\in L$ then there is $\pi_1$ with $V(x,\pi_1,\pi_2)=1$ for every $\pi_2$;
2. if $x\notin L$ then there is $\pi_2$ with $V(x,\pi_1,\pi_2)=0$ for every $\pi_1$.

$\mathrm{S}_2\mathrm{P}=\bigcup_k\mathrm{S}_2\mathrm{TIME}[n^k]$ and $\mathrm{S}_2\mathrm{E}=\bigcup_c\mathrm{S}_2\mathrm{TIME}[2^{cn}]$. One may think of two competing provers, one claiming membership and one claiming non-membership, with a referee who sees both proofs; the honest prover always wins. Directly from the definition $\mathrm{S}_2\mathrm{P}\subseteq\Sigma_2\mathrm{P}\cap\Pi_2\mathrm{P}$. The class $\mathrm{S}_2\mathrm{E}/_1$ allows one bit of advice per input length.

## Depends on

- [The universal levels of the polynomial hierarchy](../../complexity-classes/time-and-space-complexity-classes/pi-k.md)

## Sources

- Alexander Russell and Ravi Sundaram, "Symmetric alternation captures BPP", Computational Complexity 7 (1998).
- Ran Canetti, "More on BPP and the polynomial-time hierarchy", Information Processing Letters 57 (1996).
- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
