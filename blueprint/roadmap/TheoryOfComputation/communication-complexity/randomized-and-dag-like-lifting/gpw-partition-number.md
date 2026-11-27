# Göös–Pitassi–Watson: deterministic communication versus partition number

The **partition number** $\chi(F)$ of a Boolean matrix $F$ is the least number of monochromatic rectangles that partition it. There is an explicit family of total functions $F$ with

$$
D^{cc}(F) \ge \widetilde{\Omega}\bigl(\log^{1.5} \chi(F)\bigr),
$$

refuting the conjecture that deterministic communication complexity is $O(\log \chi(F))$ and showing that the Aho-Ullman-Yannakakis bound $D^{cc}(F) = O(\log^2 \chi(F))$ cannot be improved below the exponent $1.5$. The same method gives a total $F$ with $D^{cc}(F) \ge \widetilde{\Omega}\bigl(\log^{2} \chi_1(F)\bigr)$, where $\chi_1(F)$ is the least number of rectangles partitioning $F^{-1}(1)$; this is tight up to polylogarithmic factors by Yannakakis' bound $D^{cc}(F) = O(\log^2 \chi_1(F))$.

## Proof sketch

Find a Boolean function $f$ with deterministic query complexity $\widetilde{\Omega}(C(f)^{1.5})$, where $C(f)$ is the unambiguous certificate complexity, using a pointer-function construction. Lift with the index gadget via the deterministic lifting theorem: unambiguous certificates become a rectangle partition of size $2^{O(C(f)\log m)}$, while deterministic communication complexity lifts from query complexity.

## Depends on

- [Partition number and unambiguous certificate complexity](partition-number.md)

## Proof depends on

- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)

## Sources

- M. Göös, T. Pitassi, T. Watson, "Deterministic communication vs. partition number", FOCS (2015); SIAM Journal on Computing 47 (2018).
- M. Yannakakis, "Expressing combinatorial optimization problems by linear programs", Journal of Computer and System Sciences 43 (1991) 441-466.
