# Mean-payoff games on timed automata with three clocks are undecidable

No algorithm decides, given a priced timed game with three clocks, whether the value of its mean-payoff game from the initial location is below a given bound, even when every location costs $0$ or $1$ per time unit.

**Theorem.** A *priced timed game arena* (PTGA) $T = (L_{\mathrm{Min}}, L_{\mathrm{Max}}, \mathrm{Act}, X, \mathrm{Inv}, E, \rho, \delta, p)$ consists of disjoint sets of locations controlled by players Min and Max, with $L = L_{\mathrm{Min}} \cup L_{\mathrm{Max}}$; a finite set $\mathrm{Act}$ of actions; a finite set $X$ of clocks; an invariant $\mathrm{Inv}(\ell)$ (a zone) for each location; an enabling zone $E(\ell, a)$ for each location and action; a set $\rho(a) \subseteq X$ of clocks reset by each action; a transition function $\delta : L \times \mathrm{Act} \to L$; and prices $p : L \cup (L \times \mathrm{Act}) \to \mathbb{R}$. It is *binary-priced* if $p(\ell) \in \{0, 1\}$ for every location $\ell$. From a configuration $(\ell, \nu)$ with $\nu \in \mathrm{Inv}(\ell)$, the owner of $\ell$ chooses a timed action $(t, a)$ such that $\nu + t' \in \mathrm{Inv}(\ell)$ for all $t' \in [0, t]$ and $\nu + t \in E(\ell, a)$; the play moves to $(\delta(\ell, a), \nu')$, where $\nu'$ is $\nu + t$ with the clocks in $\rho(a)$ reset, and Min pays Max $p(\ell) \cdot t + p(\ell, a)$. Min minimizes $\limsup_{n \to \infty} \frac1n \sum_{i < n} \pi_i$ and Max maximizes $\liminf_{n \to \infty} \frac1n \sum_{i < n} \pi_i$, where $\pi_i$ is the price of the $i$-th move. For a PTGA $T$ and $r \in \mathbb{R}$, the problem $\mathrm{MPG}(T, r)$ asks whether the value of this mean-payoff game at the state $(\ell, \mathbf 0)$, with all clocks at zero, is smaller than $r$. Then:

1. $\mathrm{MPG}(T, 0)$ is undecidable for PTGAs $T$ with $3$ clocks whose location prices lie in $\{0, 1, -1\}$;
2. $\mathrm{MPG}(T, r)$ is undecidable for binary-priced PTGAs $T$ with $3$ clocks and $r \ge 0$.

The same holds when the payoff is averaged per time unit instead of per move (Theorem 23 of the source, with $r > 0$ in the binary-priced case). In contrast, mean-payoff games on binary-priced timed automata with one clock are decidable (Theorem 5). The bound of three clocks improves the earlier undecidability of these games with five clocks (Brenguier, Cassez and Raskin).

## Depends on

- [Timed games](../timed-games.md)
- [Zones and difference-bound matrices](../zones-and-difference-bound-matrices.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem of two-counter machines. Each instruction is a module; on entry to a module the clocks satisfy $x_1 = 1/(5^{c_1} 7^{c_2})$ and $x_2 = x_3 = 0$, where $c_1, c_2$ are the counter values. Player Min simulates an instruction by choosing a delay; for a decrement of the first counter the correct delay is $4 x_1$. After each delay, Max may continue the simulation or enter one of two check widgets; if Min's delay was off by $\varepsilon > 0$ in either direction, the matching widget is a loop whose mean cost is $\varepsilon$, so Max punishes every simulation error with a positive mean payoff, while a correct simulation costs $0$ in every module. The halting instruction leads to a location of price $1$ with a self loop. So if the machine halts, every strategy of Min yields a positive mean payoff, and if it does not halt, Min achieves mean payoff $0$ by simulating faithfully; the variants with binary prices and with the per-time-unit payoff redraw the widgets.

## Sources

- S. Guha, M. Jurdziński, S. N. Krishna and A. Trivedi, "Mean-Payoff Games on Timed Automata", in *36th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2016)*, Leibniz International Proceedings in Informatics 65, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2016, article 44, doi:[10.4230/LIPIcs.FSTTCS.2016.44](https://doi.org/10.4230/LIPIcs.FSTTCS.2016.44); read as arXiv:1607.08480v1, whose numbering is used here: Definitions 3 and 4, Section 2.1 (mean-payoff objectives), Theorem 5, Theorem 14 with its proof (Section 5 and Appendix D.1) and Theorem 23 (Appendix D.2).
