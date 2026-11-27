# Lutz's resource-bounded measure

Identify a language $A$ with its characteristic sequence along the standard enumeration $s_0=\lambda,s_1=0,s_2=1,s_3=00,\dots$. A **martingale** is $d:\{0,1\}^*\to[0,\infty)$ with $d(w)=\tfrac12\bigl(d(w0)+d(w1)\bigr)$; it **succeeds** on $A$ if $\limsup_n d(A\restriction n)=\infty$. A **p-martingale** is a martingale computable (to any precision $2^{-r}$) in time polynomial in $|w|+r$. A class $X$ has **p-measure zero** if some p-martingale succeeds on every $A\in X$, and $X$ has **measure zero in $\mathsf{E}$** if $X\cap\mathsf{E}$ has p-measure zero. p-measure-zero classes are closed under subsets and finite (indeed p-uniform countable) unions.

## Depends on

- [The class E](../../time-and-space-complexity-classes/e.md)

## Sources

- Jack H. Lutz, "Almost everywhere high nonuniform complexity", Journal of Computer and System Sciences 44(2), 1992 (original formulation with density functions).
- Jack H. Lutz, "The Quantitative Structure of Exponential Time", in Complexity Theory Retrospective II, Springer, 1997, Section 3 (the martingale formulation used here).
