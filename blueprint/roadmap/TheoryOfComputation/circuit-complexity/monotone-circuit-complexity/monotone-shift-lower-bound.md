# Monotone cyclic shift needs qn log2 n - O(qn) gates

For all $n,q,m$, every control code $\alpha$ and every monotone circuit computing the monotone cyclic shift operator $S_{q,\alpha}$ (or the monotone permutation operator for any code $\beta$), the number of binary gates is at least $q\sum_{t=1}^{n}\lceil\log_2 t\rceil\ge qn\log_2 n-qn$.

## Proof sketch

Each output bit must be able to receive each of the $n$ input bits of its column under some control; in a monotone circuit with antichain controls the paths carrying different data bits to one output cannot be merged without a gate, and a counting argument over the binary tree structure of these paths gives $\lceil\log_2 t\rceil$ gates per bit and position.

## Depends on

- [Monotone cyclic shift and permutation operators](monotone-cyclic-shift-operator.md)

## Proof depends on

- [Monotone cyclic shift in L(A) + O(qn log n) gates](monotone-shift-upper-bound.md)

## Sources

- Igor S. Sergeev, "On the Monotone Complexity of the Shift Operator", 2020.
- A. V. Chashkin, "On the Complexity of a Cyclic Shift of a Set of Real Numbers", Diskretnaya Matematika i Prilozheniya (Diskretnyi Analiz i Issledovanie Operatsii, Ser. 1), 2006.
- Edmund A. Lamagna, John E. Savage, "Combinational Complexity of Some Monotone Functions", Proceedings of the 15th Annual Symposium on Switching and Automata Theory (SWAT 1974), 1974.
