# Priced timed automata with nonlinear prices

A priced timed automaton is a timed automaton in which waiting in a location costs a price given by a function of the configuration and of the delay, not necessarily linear, and taking an edge costs a fixed integer; cost-optimal reachability asks whether a target location can be reached within a budget.

Let $X$ be a finite set of clocks; a *valuation* is a map $\nu:X\to\mathbb R_{\ge0}$, $\nu+\tau$ adds $\tau\ge0$ to every clock and $\nu[Y:=0]$ resets the clocks of $Y\subseteq X$. A *guard* is a finite conjunction of constraints $x\sim c$ with $x\in X$, $c\in\mathbb Z_{\ge0}$ and $\sim\in\{<,\le,=,>,\ge\}$. A *timed automaton* $(L,X,E,I)$ has a finite set $L$ of locations, a finite set $E\subseteq L\times G\times 2^X\times L$ of edges (guard, reset set) and an invariant $I(\ell)$ (a guard) for each location.

A *priced timed automaton* (PTA) $(L,X,E,I,\pi,\psi)$ adds a *price function* $\pi$ that gives the cost $\pi((\ell,\nu),t)\ge0$ of waiting $t\ge0$ time units from configuration $(\ell,\nu)$, and an edge price $\psi:E\to\mathbb Z_{\ge0}$. Configurations are triples $(\ell,\nu,u)$ with an accumulated price $u$. A *delay* $(\ell,\nu,u)\xrightarrow{t}(\ell,\nu+t,u+\pi((\ell,\nu),t))$ is allowed when $\nu+\delta$ satisfies $I(\ell)$ for all $0\le\delta\le t$; a *switch* along an edge $(\ell,g,Y,\ell')$ goes to $(\ell',\nu[Y:=0],u+\psi(\text{edge}))$ when $\nu$ satisfies $g$ and $I(\ell)$ and $\nu[Y:=0]$ satisfies $I(\ell')$. Runs alternate delays and switches strictly (consecutive delays cannot be merged, since $\pi$ need not be additive in $t$), and the cost $C(\rho)$ of a run is the sum of its delay and switch prices. The automaton is *linearly priced* when $\pi((\ell,\nu),t)=k_\ell t$.

For locations $\ell,\ell'$, let $\mathrm{OptCost}(\ell,\ell')=\inf_\rho C(\rho)$ over runs from $\ell$ to $\ell'$. The *cost-optimal reachability problem* asks, given a PTA, locations $\ell,\ell'$ and a budget $B$, whether $\mathrm{OptCost}(\ell,\ell')\le B$.

## Depends on

- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)

## Proof depends on

None.

## Expansion

For linearly priced timed automata cost-optimal reachability is PSPACE-complete, as the source recalls, and the source extends this to piecewise-linear prices with integer breakpoints; for Lipschitz-continuous prices on bounded clocks it decides the $\varepsilon$-approximate problem.

## Sources

- Devendra Bhave, Shankara Narayanan Krishna and Ashutosh Trivedi, "On Nonlinear Prices in Timed Automata", Electronic Proceedings in Theoretical Computer Science 232, 2016, pp. 65–78, doi:[10.4204/EPTCS.232.9](https://doi.org/10.4204/EPTCS.232.9); numbering of arXiv:1612.04976v1 ([arXiv](https://arxiv.org/abs/1612.04976v1)): Section 2: the definitions of timed automata and priced timed automata, the cost-optimal reachability problem and the $\varepsilon$-cost-optimal reachability problem, and the summary of results.
