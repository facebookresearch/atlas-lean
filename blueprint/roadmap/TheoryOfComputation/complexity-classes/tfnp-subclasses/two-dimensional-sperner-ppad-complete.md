# Chen–Deng: two-dimensional circuit Sperner is PPAD-complete

In **2D-SPERNER**, a circuit colours the points of a $2^{N}\times2^{N}$ grid (with a fixed boundary colouring using three colours as in Sperner's lemma), and a solution is a trichromatic unit triangle (or a boundary violation). 2D-SPERNER is $\mathsf{PPAD}$-complete under polynomial-time search reductions.

## Proof sketch

Membership: Sperner's path-following argument walks through bichromatic triangles, giving an END-OF-LINE instance. Hardness: embed an $n$-bit END-OF-LINE graph into a $2^{n+5}\times2^{n+5}$ grid by tiling $16\times16$ gadgets for routing wires, crossovers and line ends; trichromatic triangles appear only at gadgets encoding ends of lines.

## Depends on

- [The classes PPP, PPAD, PPADS and PPA](ppp-ppad-ppads-ppa.md)

## Proof depends on

- [Inclusions among the TFNP subclasses](tfnp-subclass-inclusions.md)

## Sources

- Xi Chen and Xiaotie Deng, "On the Complexity of 2D Discrete Fixed Point Problem", Automata, Languages and Programming (ICALP 2006), 2006.
- Xi Chen, Xiaotie Deng and Shang-Hua Teng, "Settling the Complexity of Computing Two-Player Nash Equilibria", Journal of the ACM 56(3), arXiv:0704.1678, 2009, Section 4.1.
