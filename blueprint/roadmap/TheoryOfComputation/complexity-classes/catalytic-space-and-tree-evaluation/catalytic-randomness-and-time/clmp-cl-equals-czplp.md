# Cook–Li–Mertz–Pyne: catalytic logspace equals zero-error polynomial-time catalytic logspace (CL = CZPLP)

$\mathsf{CL}=\mathsf{CZPLP}$ and $\mathsf{CZPL}=\mathsf{CZPLP}$. Thus granting a catalytic logspace machine zero-error randomness lets it run in worst-case polynomial time, and this characterizes deterministic catalytic logspace exactly; in particular $\mathsf{CL}\subseteq\mathsf{P}$ is equivalent to derandomizing $\mathsf{CZPLP}$, and $\mathsf{CZPLP}\subseteq\mathsf{ZPP}$.

## Proof sketch

The inclusion $\mathsf{CZPLP}\subseteq\mathsf{CZPL}\subseteq\mathsf{CBPL}=\mathsf{CL}$ uses the catalytic derandomization. For $\mathsf{CL}\subseteq\mathsf{CZPLP}$ one combines runtime compression with randomness: compress-or-compute is run with a polynomial time budget, and random choices replace the deterministic search that would otherwise be needed to locate a content on which the machine halts quickly, so that every run halts in polynomial time and fails with $\bot$ only with bounded probability, while the catalytic tape is restored on every path. The same argument applied to $\mathsf{CZPL}$ machines gives $\mathsf{CZPL}=\mathsf{CZPLP}$.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Cook–Li–Mertz–Pyne: randomized catalytic logspace is derandomized unconditionally (CBPL = CL)](clmp-cbpl-equals-cl.md)
- [Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape](clmp-runtime-compress-or-compute.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
