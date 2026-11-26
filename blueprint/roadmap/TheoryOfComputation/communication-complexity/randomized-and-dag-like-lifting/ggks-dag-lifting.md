# Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width

There is a gadget $g : \mathcal{X} \times \mathcal{Y} \to \{0,1\}$ on $O(\log n)$ bits such that for every unsatisfiable CNF formula $F$ on $n$ variables, the falsified-clause search problem of the lifted formula satisfies

$$
\text{min size of a rectangle-DAG for } \mathrm{Search}(F) \circ g^n \ \ge\ n^{\Omega(w(F))},
$$

where $w(F)$ is the minimum width of a resolution refutation of $F$. Consequently there are explicit monotone functions in $\mathrm{NP}$ (the CSP-satisfiability functions of lifted formulas) whose monotone circuit complexity is $2^{N^{\Omega(1)}}$ in the number $N$ of variables, and an exponential separation between monotone circuits and monotone formulas for functions in monotone $\mathrm{P}$.

## Proof sketch

Simulate a rectangle-DAG by a resolution refutation of $F$ in which each node's rectangle is replaced by the conjunction of the coordinates on which it is not blockwise dense; a pruning step enforces density at every node, using that rectangles of size at least $n^{-\text{small}}$ fraction contain dense subrectangles. Each node then yields a clause of width proportional to the logarithm of the rectangle's co-density, and the covering condition becomes a resolution step, so a small DAG gives a narrow refutation. Monotone lower bounds follow via the rectangle-DAG characterization of monotone circuits.

## Depends on

- [Resolution refutation](../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)
- [Rectangle-DAGs (dag-like communication protocols)](rectangle-dag.md)

## Proof depends on

- [Monotone circuits are rectangle-DAGs for monotone Karchmer–Wigderson games](monotone-circuit-rectangle-dag.md)
- [Ben-Sasson–Wigderson for general resolution](../../../Logic/propositional-logic/resolution-size-and-width/refutation-narrow.md)

## Sources

- A. Garg, M. Göös, P. Kamath, D. Sokolov, "Monotone circuit lower bounds from resolution", STOC (2018); Theory of Computing 16 (2020).
