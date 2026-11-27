# Counting threshold functions over a feature family

Let $g_1,\dots,g_m:X\to\{0,1\}$ be functions on a finite set $X$. A *threshold function over $(g_i)$* is $f(x)=[\sum_i a_ig_i(x)\ge\theta]$ with real $a_i,\theta$. Such an $f$ is determined by its *Chow moments* $\sum_{x}(-1)^{f(x)}\cdot(1,g_1(x),\dots,g_m(x))$; consequently the number of threshold functions over $(g_i)$ is at most $(2|X|+1)^{m+1}$. For linear threshold functions on $\{0,1\}^n$ this gives at most $2^{n^2+O(n\log n)}$ of them.

## Proof sketch

Since $X$ is finite, the threshold $\theta$ of $f$ can be perturbed so that $\sum_ia_ig_i(x)\ne\theta$ for all $x$. If a different threshold function $f'$ over the same features had the same Chow moments, the weighted sum $\sum_x(f(x)-f'(x))(\sum_ia_ig_i(x)-\theta)$ would vanish, being a linear combination of moment differences, yet every nonzero term is positive. Each moment coordinate is an integer of absolute value at most $|X|$.

## Depends on

- [Threshold gates and the basis of threshold circuits](../../parallel-circuit-hierarchies/threshold-gates-and-threshold-circuits.md)

## Sources

- Daniel M. Kane, Ryan Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the Forty-Eighth Annual ACM Symposium on Theory of Computing (STOC 2016), 2016 (Theorem 2.2, Chow's theorem, and Theorem 2.3, the Roychowdhury–Siu–Orlitsky count $(2^n+1)^{s+1}$ of threshold functions over $s$ given functions).
- C. K. Chow, "On the Characterization of Threshold Functions", Proceedings of the 2nd Annual Symposium on Switching Circuit Theory and Logical Design (FOCS 1961), 1961.
