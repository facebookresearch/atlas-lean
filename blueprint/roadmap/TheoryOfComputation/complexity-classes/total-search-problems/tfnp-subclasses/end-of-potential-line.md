# End-of-Potential-Line and the classes EOPL and SOPL

An **END-OF-POTENTIAL-LINE** instance consists of circuits $P,S$ (as in END-OF-LINE) and a potential $V:\{0,1\}^n\to\{0,\dots,2^m-1\}$; arcs along which the potential does not strictly increase are pruned. Solutions are ends of lines of the pruned graph other than $0^n$, and **SINK-OF-POTENTIAL-LINE** accepts only sinks. $\mathsf{EOPL}$ and $\mathsf{SOPL}$ are the search-reduction closures of these problems. Every instance can be normalized in polynomial time (on $n+1$ bits) so that $P(0^{n+1})=0^{n+1}\ne S(0^{n+1})$ and $V(0^{n+1})=0$, with solutions mapped back. One has $\mathsf{EOPL}\subseteq\mathsf{SOPL}$ (every sink of the pruned graph is also an end of a line), $\mathsf{SOPL}\subseteq\mathsf{PLS}\cap\mathsf{PPADS}$ and $\mathsf{EOPL}\subseteq\mathsf{PLS}\cap\mathsf{PPAD}$, since the pruned graph is at once a sink-of-line instance (resp. an end-of-line instance) and a local search instance with potential $V$.

## Depends on

- [The classes PPP, PPAD, PPADS and PPA](ppp-ppad-ppads-ppa.md)
- [The class PLS of polynomial local search problems](../the-class-pls-of-polynomial-local-search.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", Journal of Computer and System Sciences 114, arXiv:1811.03841, 2020, Definition 9.
- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Further Collapses in TFNP", 37th Computational Complexity Conference (CCC 2022), arXiv:2202.07761, 2022; SIAM Journal on Computing 53(3), 2024.
