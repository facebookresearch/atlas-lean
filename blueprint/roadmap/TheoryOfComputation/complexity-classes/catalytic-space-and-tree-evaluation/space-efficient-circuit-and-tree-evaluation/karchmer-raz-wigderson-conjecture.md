# The Karchmer–Raz–Wigderson composition conjecture for formula depth

For a Boolean function $f$, let $\mathsf{D}(f)$ be its minimum depth as a formula over the de Morgan basis with fan-in two. For $f:\{0,1\}^m\to\{0,1\}$ and $g:\{0,1\}^n\to\{0,1\}$ the block composition $f\diamond g:\{0,1\}^{mn}\to\{0,1\}$ is $(f\diamond g)(x_1,\dots,x_m)=f(g(x_1),\dots,g(x_m))$ with $x_i\in\{0,1\}^n$. Trivially $\mathsf{D}(f\diamond g)\le\mathsf{D}(f)+\mathsf{D}(g)$. The **KRW conjecture** (Karchmer, Raz and Wigderson, 1995) asserts that this is essentially tight: in its strong form,

$$
\mathsf{D}(f\diamond g)\ge\mathsf{D}(f)+\mathsf{D}(g)-O(1)\quad\text{for all non-constant } f,g,
$$

and weaker forms replace the additive loss by a multiplicative factor, as in $\mathsf{D}(f\diamond g)\ge \mathsf{D}(f)+\delta\,\mathsf{D}(g)$ for a constant $\delta\gt 0$. It is a hypothesis, open in general; it implies that Tree Evaluation, an iterated composition, requires formula depth $\omega(\log n)$ and hence is not in $\mathsf{NC}^1$.

## Depends on

- [The class NC^k](../../time-and-space-complexity-classes/nck.md)

## Sources

- James Cook and Ian Mertz, "Tree Evaluation Is in Space O(log n · log log n)", STOC (2024), ECCC TR23-174.
