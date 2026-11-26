# Monotone cyclic shift operator

Let $X=(x_0,\dots,x_{n-1})$ be $n$ Boolean vectors of length $q$ and let $\alpha:\{0,\dots,n-1\}\to\{0,1\}^m$ be an injective *control code* whose image is an antichain. A circuit with $nq+m$ inputs computes the *monotone cyclic shift operator* $S_{q,\alpha}$ if, for every $X$ and every $k$, on input $(X,\alpha(k))$ it outputs the cyclic shift of $X$ by $k$ blocks (block $x_i$ moved to position $i+k\bmod n$). Monotone complexity counts binary AND/OR gates.

## Depends on

- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Sources

- Igor S. Sergeev, "On the Monotone Complexity of the Shift Operator", 2020.
- Edmund A. Lamagna, John E. Savage, "Combinational Complexity of Some Monotone Functions", Proceedings of the 15th Annual Symposium on Switching and Automata Theory (SWAT 1974), 1974.
