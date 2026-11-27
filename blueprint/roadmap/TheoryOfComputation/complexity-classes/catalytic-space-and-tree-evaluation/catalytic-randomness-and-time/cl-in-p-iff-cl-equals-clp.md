# CL ⊆ P iff CL = CLP, and ZPP = P implies CL = CLP

The following hold:

1. $\mathsf{CL}\subseteq\mathsf{P}$ if and only if $\mathsf{CL}=\mathsf{CLP}$; thus any proof that catalytic logspace is in polynomial time automatically yields catalytic algorithms running in worst-case polynomial time.
2. If $\mathsf{ZPP}=\mathsf{P}$ then $\mathsf{CL}=\mathsf{CLP}$.

## Proof sketch

If $\mathsf{CL}\subseteq\mathsf{P}$ then $\mathsf{CL}=\mathsf{CL}\cap\mathsf{P}=\mathsf{CLP}$ by the Cook–Li–Mertz–Pyne theorem, and conversely $\mathsf{CLP}\subseteq\mathsf{P}$ trivially. For the second item use $\mathsf{CL}\subseteq\mathsf{ZPP}$, from the random-content runtime bound.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)
- [Polynomial time on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/p.md)
- [ZPP](../../time-and-space-complexity-classes/zpp.md)

## Proof depends on

- [Cook–Li–Mertz–Pyne: catalytic logspace and polynomial time are simultaneously achievable (CL ∩ P = CLP)](clmp-cl-cap-p-equals-clp.md)
- [Buhrman et al.: a random catalytic content gives expected running time 2^{O(s)}, hence CL is in ZPP](random-catalytic-content-expected-runtime.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
