# Cook–Li–Mertz–Pyne: catalytic logspace and polynomial time are simultaneously achievable (CL ∩ P = CLP)

$\mathsf{CL}\cap\mathsf{P}=\mathsf{CLP}$: every language decidable both by a catalytic logspace machine and by a polynomial-time machine is decidable by a catalytic logspace machine that runs in polynomial time on every input and every initial catalytic content.

## Proof sketch

Given $L\in\mathsf{CL}\cap\mathsf{P}$ with $\mathsf{CL}$ machine $M$, apply the compress-or-compute procedure to successive segments of an enlarged catalytic tape. Each attempt either computes $L(x)$ in polynomial time or frees one bit; after polynomially many compressions enough bits are free to run the polynomial-time algorithm for $L$ using them as ordinary memory. All compressions are then undone in reverse order, each in polynomial time, so the total time is polynomial for every initial content.

## Depends on

- [Polynomial time on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/p.md)
- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape](clmp-runtime-compress-or-compute.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
