# Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP

Recall catalytic logspace: $\mathsf{CL}=\bigcup_d\mathsf{CSPACE}[d\log n,n^d]$, with a read-only input, an $O(\log n)$-cell work tape, and a polynomial-length catalytic tape whose arbitrary initial content $\tau$ must be restored at the end. Define:

- $\mathsf{CLP}$: languages (or functions) computed by $\mathsf{CL}$ machines that additionally halt within $\mathrm{poly}(n)$ steps for **every** input $x$ and every initial content $\tau$;
- $\mathsf{CZPL}$: languages computed by zero-error randomized catalytic logspace machines with read-once random bits, which for every $x$ and $\tau$ output $L(x)$ or $\bot$, never a wrong answer, output $\bot$ with probability at most $1/2$, and restore $\tau$ on every random path;
- $\mathsf{CZPLP}$: the subclass of $\mathsf{CZPL}$ whose machines halt within $\mathrm{poly}(n)$ steps for every $x$, $\tau$ and random string.

Trivially $\mathsf{CLP}\subseteq\mathsf{CL}\cap\mathsf{P}$ and $\mathsf{CLP}\subseteq\mathsf{CZPLP}\subseteq\mathsf{ZPP}$.

## Depends on

- [Deterministic logarithmic space](../../time-and-space-complexity-classes/log-space.md)
- [Polynomial time on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/p.md)
- [ZPP](../../time-and-space-complexity-classes/zpp.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
- Aryan Agarwala and Ian Mertz, "Bipartite Matching is in Catalytic Logspace", arXiv:2504.09991 (2025), ECCC TR25-048.
