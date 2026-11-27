# Cook–Li–Mertz–Pyne: catalytic logspace and polynomial time are simultaneously achievable (CL ∩ P = CLP)

$\mathsf{CL}\cap\mathsf{P}=\mathsf{CLP}$: every language decidable both by a catalytic logspace machine and by a polynomial-time machine is decidable by a catalytic logspace machine that runs in polynomial time on every input and every initial catalytic content.

## Proof sketch

Given $L\in\mathsf{CL}\cap\mathsf{P}$ with $\mathsf{CL}$ machine $M$ ($s = O(\log n)$) and a polynomial-time decider running in space $B = \mathrm{poly}(n)$, invoke $\mathrm{DetComp}_w(1^B, x)$ from the compress-or-compute theorem on an enlarged catalytic tape. In worst-case time $\mathrm{poly}(2^s, B) = \mathrm{poly}(n)$ and $O(\log n)$ additional workspace, $\mathrm{DetComp}$ either returns $L(x)$ directly with the tape restored, or frees $B$ zeroed catalytic bits. In the second case, run the polynomial-time algorithm for $L$ inside those $B$ free bits, clear them back to $0^B$, and call $\mathrm{DetDecomp}_{w' \circ 0^B}(1^B, x)$ to restore $w$ in worst-case time $\mathrm{poly}(n)$ via the reversible Euler-tour walk.

## Depends on

- [Polynomial time on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/p.md)
- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape](clmp-runtime-compress-or-compute.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
