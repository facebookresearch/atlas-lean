# Chen–Deng: two-dimensional circuit Sperner is PPAD-complete

In **2D-SPERNER**, an instance $(F,0^k)$ consists of a polynomial-time machine (or circuit) $F$ that colours the points of the standard triangulation of a $2^{k}\times 2^{k}$ grid with colours $\{0,1,2\}$, the colouring being admissible (the boundary is coloured as in Sperner's lemma); a solution is a trichromatic unit triangle. Sperner's lemma guarantees a solution, and 2D-SPERNER is $\mathsf{PPAD}$-complete under polynomial-time search reductions.

## Proof sketch

Membership (Papadimitriou): Sperner's path-following argument walks through triangles carrying both colours $1$ and $2$ from the boundary, giving an END-OF-LINE instance whose ends are trichromatic triangles. Hardness: first reduce the directed leaf problem LEAFD to its restriction RLEAFD, in which the input graph is a subgraph of a fixed planar grid graph obtained by drawing a complete graph in the grid with a two-state switch gadget at every crossing of two paths; then embed such a grid graph into the triangulated grid by colouring the images of its paths with colour $0$ and all other points carefully with colours $1$ and $2$, so that a trichromatic triangle can occur only next to the image of a directed leaf.

## Depends on

- [The classes PPP, PPAD, PPADS and PPA](ppp-ppad-ppads-ppa.md)

## Sources

- Xi Chen and Xiaotie Deng, "On the Complexity of 2D Discrete Fixed Point Problem", Automata, Languages and Programming (ICALP 2006), Lecture Notes in Computer Science 4051, 2006, Definition 4 and Theorem 1; journal version Theoretical Computer Science 410(44), 2009.
- Christos H. Papadimitriou, "On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence", Journal of Computer and System Sciences 48(3), 1994.
