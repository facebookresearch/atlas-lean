# The KKT search problem for smooth objectives on bounded polytopes with Taylor-violation witnesses

Let $D=\{x\in\mathbb{R}^n:Ax\le b\}$ with $(A,b)\in\mathbb{Q}^{m\times n}\times\mathbb{Q}^m$ bounded and non-empty. For $\varepsilon\ge0$, a point $x$ is an **$\varepsilon$-KKT point** of $\min_D f$ if $x\in D$ and there is $\mu\in\mathbb{R}^m_{\ge0}$ with

$$
\|\nabla f(x)+A^{\top}\mu\|_2\le\varepsilon\quad\text{and}\quad\langle\mu,Ax-b\rangle=0 .
$$

If no constraint is tight this says $\|\nabla f(x)\|\le\varepsilon$. Membership is decidable in polynomial time by a convex quadratic program in $\mu$; using $\ell_1$ or $\ell_\infty$ instead gives polynomially equivalent problems.

**KKT.** Input: $\varepsilon>0$ and $L>0$ in binary, $(A,b)$, and well-behaved arithmetic circuits for $f:\mathbb{R}^n\to\mathbb{R}$ and $\nabla f:\mathbb{R}^n\to\mathbb{R}^n$. Output: an $\varepsilon$-KKT point, or a violation: $x,y\in D$ with $|f(x)-f(y)|>L\|x-y\|$ or $\|\nabla f(x)-\nabla f(y)\|>L\|x-y\|$, or $x,y\in D$ contradicting the Taylor bound valid for every $C^1$ function with $L$-Lipschitz gradient on convex $D$:

$$
|f(y)-f(x)-\langle\nabla f(x),y-x\rangle|\le\tfrac{L}{2}\|y-x\|^2 .
$$

Totality: $D$ is compact, so $f$ has a local minimum on $D$, which satisfies the KKT conditions for linear constraints.

## Depends on

- [Karush–Kuhn–Tucker conditions for inequality constraints](../../../../Analysis/convex-analysis-and-variations/karush-kuhn-tucker-inequality.md)
- [Well-behaved arithmetic circuits and Lipschitz violation witnesses for continuous total search problems](well-behaved-arithmetic-circuits.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
