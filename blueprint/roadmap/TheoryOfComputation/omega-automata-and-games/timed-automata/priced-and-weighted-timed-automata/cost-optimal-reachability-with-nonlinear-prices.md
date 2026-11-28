# Zero-cost reachability in nonlinearly priced timed automata is undecidable

No algorithm decides, for priced timed automata whose waiting prices are polynomials in the clocks and the delay, whether a target location is reachable by a run of cost exactly zero; the source states this as undecidability of cost-optimal reachability for nonlinear prices.

**Theorem.** No algorithm decides, given a [priced timed automaton with nonlinear prices](priced-timed-automata-with-nonlinear-prices.md) with four clocks whose waiting prices are nonnegative polynomials with rational coefficients in the clock values and the delay, given by their coefficients, together with locations $\ell, \ell'$, whether some run from $\ell$, with all clocks $0$, to $\ell'$ has cost exactly $0$. This is what the proof of Theorem 2.1 of the source displays: a two-counter machine reaches its target configuration iff the constructed automaton has a run from $q$ to $q'$ of cost exactly zero (Section 3 of the source). The source states Theorem 2.1 as undecidability of the cost-optimal reachability problem $\mathrm{OptCost}(\ell, \ell') \le B$, where $\mathrm{OptCost}(\ell, \ell')$ is the infimum of the costs of runs from $\ell$ to $\ell'$; for the reduction's automata that form with $B = 0$ would also need non-halting machines to admit no runs of arbitrarily small positive cost, which the source does not discuss.

The prices of the reduction are squares of affine expressions in one clock and the delay, such as $(1-x-2t)^2$ and $(1-x-t/2)^2$. For linear and piecewise-linear prices the problem is PSPACE-complete.

## Depends on

- [Priced timed automata with nonlinear prices](priced-timed-automata-with-nonlinear-prices.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem of two-counter machines. Clocks $x$ and $y$ encode the counters $c,d$ as $1-2^{-c}$ and $1-2^{-d}$, with two auxiliary clocks $w,z$; testing $c=0$ is testing $x=0$. Each instruction is a module. In the increment module the automaton waits $t$ in a location priced $(1-x-2t)^2$, which is $0$ exactly when $t=(1-x)/2$, so that the new value of $c+1$ is copied to $w$; the decrement module uses $(1-x-t/2)^2$, forcing $t=2^{-(c-1)}$. Self-loops resetting $y$ at $1$ keep the other counter intact. A run costs $0$ exactly when every wait is the correct one, so the target configuration of the machine is reachable iff the automaton reaches its target location by a run of cost $0$; the roles of $x$ and $w$ swap from one module to the next. Whether the infimum form $\mathrm{OptCost} \le 0$ also holds for these automata is open here: a waiting error $\delta$ in the decrement module costs only $O(\delta^2)$, so a good expansion would have to show that non-halting machines give no runs of arbitrarily small positive cost.

## Sources

- Devendra Bhave, Shankara Narayanan Krishna and Ashutosh Trivedi, "On Nonlinear Prices in Timed Automata", Electronic Proceedings in Theoretical Computer Science 232, 2016, pp. 65–78, doi:[10.4204/EPTCS.232.9](https://doi.org/10.4204/EPTCS.232.9); numbering of arXiv:1612.04976v1 ([arXiv](https://arxiv.org/abs/1612.04976v1)): Section 2, Theorem 2.1 (undecidability for nonlinearly priced timed automata), and its proof in Section 3.
