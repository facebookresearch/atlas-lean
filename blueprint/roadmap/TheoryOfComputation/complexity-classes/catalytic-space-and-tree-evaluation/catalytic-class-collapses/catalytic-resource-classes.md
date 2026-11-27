# Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes

For $s=s(n)$ and $c=c(n)$ let $\mathsf{CSPACE}[s,c]$ be the class of languages decided by deterministic catalytic machines with free space $s$ and catalytic space $c$, and let $\mathsf{CNSPACE}[s,c]$, $\mathsf{coCNSPACE}[s,c]$, $\mathsf{CBPSPACE}[s,c]$, $\mathsf{CPrSPACE}[s,c]$ and $\mathsf{CZPSPACE}[s,c]$ be the classes of languages whose characteristic functions are computed, respectively, nondeterministically, co-nondeterministically, with bounded error, with unbounded error, and with zero error by valid catalytic machines with these resources. Random bits are read once, as in ordinary randomized space. The logarithmic-space instantiations are

$$
\mathsf{CL}=\bigcup_{d\in\mathbb{N}}\mathsf{CSPACE}[d\log n,\,n^{d}],\qquad \mathsf{CNL}=\bigcup_{d\in\mathbb{N}}\mathsf{CNSPACE}[d\log n,\,n^{d}],
$$

and analogously $\mathsf{coCNL}$, $\mathsf{CBPL}$, $\mathsf{CPrL}$ and $\mathsf{CZPL}$. Taking $c=0$ recovers the ordinary classes $\mathsf{NSPACE}[s]$, $\mathsf{BPSPACE}[s]$ and $\mathsf{PrSPACE}[s]$. Directly from the definitions, $\mathsf{CL}\subseteq\mathsf{CZPL}\subseteq\mathsf{CBPL}\subseteq\mathsf{CPrL}$ and $\mathsf{CL}\subseteq\mathsf{CNL}\cap\mathsf{coCNL}$, where $\mathsf{CZPL}\subseteq\mathsf{CBPL}$ uses two independent runs to push the probability of $\bot$ below $1/4$.

## Depends on

- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)
- [Nondeterministic space classes](../../time-and-space-complexity-classes/nspace.md)
- [The complexity class NL](../../time-and-space-complexity-classes/nl.md)
- [Probabilistic polynomial time with unbounded error](../../time-and-space-complexity-classes/pp.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
- Samir Datta, Chetan Gupta, Rahul Jain, Vimal Raj Sharma and Raghunath Tewari, "Randomized and Symmetric Catalytic Computation", CSR (2020), ECCC TR20-024.
- Harry Buhrman, Michal Koucký, Bruno Loff and Florian Speelman, "Catalytic Space: Non-determinism and Hierarchy", Theory of Computing Systems 62(1) (2018).
