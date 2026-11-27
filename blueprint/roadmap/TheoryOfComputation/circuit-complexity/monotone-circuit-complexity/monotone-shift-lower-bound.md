# Monotone cyclic shift needs Ω(n log n) gates

There is a constant $c>0$ such that for all $n\ge 2$, every monotone circuit computing the monotone cyclic shift operator $S_{1,\alpha}$ on $n$ Boolean inputs with the one-hot control code $\alpha(k)=e_k$ (so $m=n$ and output $j$ is $\bigvee_k(c_k\wedge x_{j-k\bmod n})$) has at least $c\,n\log_2 n$ binary gates. Since a circuit of $O(n\log n)$ gates computes it, its monotone complexity is $\Theta(n\log n)$.

## Proof sketch

With the control set to $e_k$, a monotone circuit for the shift must carry each input $x_i$ to the output $i+k\bmod n$ along a path of gates, for every $k$. A counting argument over these paths for all $n$ shifts at once shows that the gates cannot be shared enough to avoid $\Omega(\log n)$ gates per input on average.

## Depends on

- [Monotone cyclic shift operator](monotone-cyclic-shift-operator.md)

## Sources

- Edmund A. Lamagna, John E. Savage, "Combinational Complexity of Some Monotone Functions", Proceedings of the 15th Annual Symposium on Switching and Automata Theory (SWAT 1974), 1974.
- Nicholas Pippenger, Leslie G. Valiant, "Shifting Graphs and Their Applications", Journal of the ACM 23(3), 1976.
- Igor S. Sergeev, "On the Monotone Complexity of the Shift Operator", arXiv:1905.10747, 2020 (preprint; Theorem 3, $L(S_{q,A})\ge qn\log_2 n-O(qn)$ for every antichain $A$, and the $O(n\log n)$ upper bound for the one-hot code).
