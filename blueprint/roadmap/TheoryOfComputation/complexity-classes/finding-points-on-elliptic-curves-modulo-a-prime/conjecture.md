# Finding a point on an elliptic curve modulo a prime

The statement asks whether points on elliptic curves modulo a prime can be found deterministically in polynomial time. Precisely: there is a single function $A : \mathbb{N}^3 \to \mathbb{N}^2$ such that

- $A$ is computed in time polynomial in the length of the encoded input by a deterministic Turing machine with a finite set of stacks and distinguished input and output stacks, with the input triple and the output pair encoded in binary through their standard natural-number codes; and
- for all natural numbers $a, b, p$ with $p$ prime and the curve $y^2 = x^3 + ax + b$ nonsingular modulo $p$: if the curve has some point $(x, y)$ with $x, y < p$ modulo $p$, then $A(a, b, p) = (x_0, y_0)$ is such a point, that is, $x_0, y_0 < p$ and $y_0^2 \equiv x_0^3 + a x_0 + b \pmod p$.

Nothing is required of the output when the curve has no affine point modulo $p$. It holds; the resolution is [Polynomial-time point finding on elliptic curves modulo a prime](conjecture-holds.md).

## Sources

- L. M. Adleman and K. S. McCurley, "Open Problems in Number Theory Complexity, II", Algorithmic Number Theory (ANTS-I), Lecture Notes in Computer Science 877 (1994), p. 307. https://mccurley.org/papers/open.ps.gz
