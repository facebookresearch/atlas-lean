# Cook–Li–Mertz–Pyne: randomized catalytic logspace is derandomized unconditionally (CBPL = CL)

$\mathsf{CBPL}=\mathsf{CL}$, where $\mathsf{CBPL}$ is bounded-error catalytic logspace with read-once random bits and restoration of the catalytic tape on every random path. More generally the same method shows $\mathsf{CBPSPACE}[s,c]\subseteq\mathsf{CSPACE}[O(s),O(c)]$ when $c=2^{\Theta(s)}$; previously $\mathsf{CBPL}=\mathsf{CL}$ was known only under strong circuit lower bounds (Datta–Gupta–Jain–Sharma–Tewari).

## Proof sketch

The proof is a compress-or-compress-or-random argument. First, runtime compression either computes quickly or frees space, so one may assume the randomized machine halts quickly on the current content. Second, part of the catalytic tape is used as the seed of a pseudorandom generator with small-space deterministic reconstruction (a Nisan–Wigderson-type generator with a distinguish-to-predict transformation): if the generator fools the machine on this content, averaging its outputs decides the language; if not, the reconstruction procedure turns the distinguisher into a short description of the seed, i.e. a compression of the tape, from which the original content is recoverable.

## Depends on

- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape](clmp-runtime-compress-or-compute.md)
- [Pseudorandom generators with logarithmic seed derandomize BPP](../../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-with-logarithmic-seed.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
- Samir Datta, Chetan Gupta, Rahul Jain, Vimal Raj Sharma and Raghunath Tewari, "Randomized and Symmetric Catalytic Computation", CSR (2020), ECCC TR20-024.
