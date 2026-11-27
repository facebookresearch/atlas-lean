# Polynomial-time point finding on elliptic curves modulo a prime

This result proves the proposition stated as [Finding a point on an elliptic curve modulo a prime](conjecture.md). Precisely, there is a single function $A : \mathbb{N}^3 \to \mathbb{N}^2$, computed in time polynomial in the length of the encoded input by a deterministic Turing machine with a finite set of stacks and distinguished input and output stacks (with inputs and outputs encoded in binary through their standard natural-number codes), such that for all natural numbers $a, b, p$ with $p$ prime and $y^2 = x^3 + ax + b$ nonsingular modulo $p$, whenever the curve has a point $(x, y)$ with $x, y < p$ modulo $p$, the output $A(a, b, p) = (x_0, y_0)$ satisfies $x_0, y_0 < p$ and

$$y_0^2 \equiv x_0^3 + a x_0 + b \pmod p.$$

The algorithm of Shallue and van de Woestijne, which computes a rational point on an elliptic curve over a finite field from a Weierstrass equation, is the one meant.

## Sources

- L. M. Adleman and K. S. McCurley, "Open Problems in Number Theory Complexity, II", Algorithmic Number Theory (ANTS-I), Lecture Notes in Computer Science 877 (1994), p. 307. https://mccurley.org/papers/open.ps.gz
- A. Shallue and C. E. van de Woestijne, "Construction of rational points on elliptic curves over finite fields", ANTS VII, Lecture Notes in Computer Science 4076 (2006), 510–524. https://doi.org/10.1007/11792086_36
