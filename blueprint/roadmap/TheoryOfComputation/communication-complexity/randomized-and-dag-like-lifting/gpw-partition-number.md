# Göös–Pitassi–Watson: deterministic communication versus partition number

The **partition number** $\chi(F)$ of a Boolean matrix $F$ is the least number of monochromatic rectangles that partition it. There is an explicit family of total functions $F$ with

$$
D^{cc}(F) \ge \widetilde{\Omega}\bigl(\log^{1.5} \chi(F)\bigr),
$$

refuting the conjecture that deterministic communication complexity is $O(\log \chi(F))$ and showing that the Aho-Ullman-Yannakakis bound $D^{cc}(F) = O(\log^2 \chi(F))$ cannot be improved below the exponent $1.5$. The result also gives a superpolynomial separation between chromatic number and biclique-partition-type quantities related to the Alon-Saks-Seymour problem.

## Proof sketch

Find a Boolean function $f$ with deterministic query complexity $\widetilde{\Omega}(C(f)^{1.5})$, where $C(f)$ is the unambiguous certificate complexity, using a pointer-function construction. Lift with the index gadget via the deterministic lifting theorem: unambiguous certificates become a rectangle partition of size $2^{O(C(f)\log m)}$, while deterministic communication complexity lifts from query complexity.

## Depends on

- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)
- [Partition number and unambiguous certificate complexity](partition-number.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Proof depends on

- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)
- [Partition number and unambiguous certificate complexity](partition-number.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- M. Göös, T. Pitassi, T. Watson, "Deterministic communication vs. partition number", FOCS (2015); SIAM Journal on Computing 47 (2018).
