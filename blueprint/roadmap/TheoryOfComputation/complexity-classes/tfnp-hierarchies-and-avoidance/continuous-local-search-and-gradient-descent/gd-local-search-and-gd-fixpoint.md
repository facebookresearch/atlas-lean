# GD-LOCAL-SEARCH and GD-FIXPOINT: termination points of projected gradient descent with fixed step size

Both problems take $\varepsilon>0$, a step size $\eta>0$, a bounded polytope $D$, well-behaved circuits for $f$ and $\nabla f$, and $L>0$, and both accept the same violations as KKT (Lipschitz violations of $f$ or $\nabla f$, and pairs contradicting the Taylor bound). Writing $x'=\Pi_D(x-\eta\nabla f(x))$ for the projected gradient step:

- **GD-LOCAL-SEARCH** asks for $x\in D$ with $f(x')\ge f(x)-\varepsilon$ (descent improves by less than $\varepsilon$);
- **GD-FIXPOINT** asks for $x\in D$ with $\|x-x'\|\le\varepsilon$ (an approximate fixed point of the dynamics).

Both are total because a local minimum of $f$ on $D$ satisfies both stopping rules. If the Taylor violation is dropped, GD-LOCAL-SEARCH keeps its complexity, whereas GD-FIXPOINT and KKT become PPAD-complete (set $f\equiv0$ and $\nabla f(x)=x-h(x)$ for a Brouwer map $h$).

## Depends on

- [The KKT search problem for smooth objectives on bounded polytopes with Taylor-violation witnesses](kkt-search-problem.md)

## Sources

- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
