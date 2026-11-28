# Cost-optimal reachability in nonlinearly priced timed automata is undecidable

No algorithm decides, for priced timed automata whose waiting prices are nonlinear functions of the clocks and the delay, whether a target location is reachable with optimal cost within a given budget.

**Theorem.** The cost-optimal reachability problem for [priced timed automata with nonlinear prices](priced-timed-automata-with-nonlinear-prices.md) is undecidable (Theorem 2.1 of the source). Since a general price function is not a finite object, the statement is meant for the prices of the reduction: no algorithm decides, given a priced timed automaton with four clocks whose waiting prices are nonnegative polynomials with rational coefficients in the clock values and the delay (as the linked definition and the source require), given by their coefficients, together with locations $\ell,\ell'$, whether $\mathrm{OptCost}(\ell,\ell')\le 0$.

The prices of the reduction are squares of affine expressions in one clock and the delay, such as $(1-x-2t)^2$ and $(1-x-t/2)^2$. For linear and piecewise-linear prices the problem is PSPACE-complete.

## Depends on

- [Priced timed automata with nonlinear prices](priced-timed-automata-with-nonlinear-prices.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem of two-counter machines. Clocks $x$ and $y$ encode the counters $c,d$ as $1-2^{-c}$ and $1-2^{-d}$, with two auxiliary clocks $w,z$; testing $c=0$ is testing $x=0$. Each instruction is a module. In the increment module the automaton waits $t$ in a location priced $(1-x-2t)^2$, which is $0$ exactly when $t=(1-x)/2$, so that the new value of $c+1$ is copied to $w$; the decrement module uses $(1-x-t/2)^2$, forcing $t=2^{-(c-1)}$. Self-loops resetting $y$ at $1$ keep the other counter intact. A run costs $0$ exactly when every wait is the correct one, so the target configuration of the machine is reachable iff the automaton reaches its target location with cost $0$, and the optimal cost is then at most $0$; the roles of $x$ and $w$ swap from one module to the next. The source's argument concerns runs of cost exactly $0$; it does not discuss runs of positive but arbitrarily small cost, which matter for the infimum.

## Sources

- Devendra Bhave, Shankara Narayanan Krishna and Ashutosh Trivedi, "On Nonlinear Prices in Timed Automata", Electronic Proceedings in Theoretical Computer Science 232, 2016, pp. 65–78, doi:[10.4204/EPTCS.232.9](https://doi.org/10.4204/EPTCS.232.9); numbering of arXiv:1612.04976v1 ([arXiv](https://arxiv.org/abs/1612.04976v1)): Section 2, Theorem 2.1 (undecidability for nonlinearly priced timed automata), and its proof in Section 3.
