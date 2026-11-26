# CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou

**CONTINUOUS-LOCALOPT.** Input: $\varepsilon>0$, a Lipschitz constant $L>0$ and well-behaved arithmetic circuits $p:[0,1]^n\to[0,1]$ and $g:[0,1]^n\to[0,1]^n$. Output: a point $x\in[0,1]^n$ with

$$
p(g(x))\ \ge\ p(x)-\varepsilon ,
$$

or a violation: $x,y$ with $|p(x)-p(y)|>L\|x-y\|$, or $x,y$ with $\|g(x)-g(y)\|>L\|x-y\|$. For fixed $k$, $k$D-CONTINUOUS-LOCALOPT fixes $n=k$.

**GENERAL-CONTINUOUS-LOCALOPT** replaces $[0,1]^n$ by a bounded non-empty polytope $D=\{x:Ax\le b\}$ given by rational $(A,b)$, takes circuits $p:\mathbb{R}^n\to\mathbb{R}$, $g:\mathbb{R}^n\to\mathbb{R}^n$, and asks for $x\in D$ with $p(\Pi_D(g(x)))\ge p(x)-\varepsilon$ (or a violation on $D$), where $\Pi_D$ is Euclidean projection onto $D$, computable exactly in polynomial time as a convex quadratic program.

**CLS** (continuous local search) is the class of total search problems polynomial-time reducible to 3D-CONTINUOUS-LOCALOPT. Intuitively $g$ proposes a local improvement step and $p$ is a Lipschitz potential, so CLS merges the local-search structure of PLS with the continuous fixed-point structure of PPAD.

## Depends on

- [Well-behaved arithmetic circuits and Lipschitz violation witnesses for continuous total search problems](well-behaved-arithmetic-circuits.md)
- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [The class PLS of polynomial local search problems](../../total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Sources

- Constantinos Daskalakis and Christos H. Papadimitriou, "Continuous Local Search", SODA (2011).
- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
