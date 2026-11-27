# Two-way transducers and MSO-definable string transductions

A *two-way finite state transducer* (two-way generalized sequential machine, 2gsm) is a finite automaton with a two-way read-only input tape,
delimited by end-markers, and a one-way output tape; it moves freely over the input, may reverse or copy parts of it (for example it realizes
$w \mapsto ww$), and defines a string transduction; $\mathrm{2DGSM}$ is the class of transductions realized by deterministic ones. A string
transduction is *MSO-definable* (class $\mathrm{MSOS}$) if it is given, with each word $w$ represented by the linear graph with $|w| + 1$ nodes whose
$|w|$ edges carry the letters of $w$ (so the empty word is a single node), by a closed domain formula of
[monadic second-order logic](../../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md), a finite copy set $C$, node formulas $\varphi^c(x)$ choosing which copies of the
input nodes are kept, and edge formulas $\varphi^{c_1, c_2}_\gamma(x, y)$ defining the edges of the output graph, labelled by output letters $\gamma$, between copies; the
output must again represent a string in the same way. With the representation by labelled positions instead, the empty input could only be mapped
to the empty output. Allowing free set variables as parameters gives the nondeterministic class $\mathrm{NMSOS}$.

## Depends on

- [Monadic second-order logic over words](../../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Sources

- J. Engelfriet and H. J. Hoogeboom, "MSO definable string transductions and two-way finite-state transducers", *ACM Transactions on Computational Logic* 2(2), 2001; numbering of the technical report version, Leiden University TR 98-13, arXiv:cs/9906007: the introduction and Section 2 (two-way generalized sequential machines) and Section 3 (mso definable string transductions: domain formula, copy set, node and edge formulas, Definitions 10 and 13) and Section 5 (the parametrized nondeterministic version).
