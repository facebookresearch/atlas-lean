# Winning priced timed games with negative prices is undecidable

No algorithm decides whether Player 1 has a winning strategy in a priced timed game with constrained-price reachability, bounded-time
reachability or repeated reachability objectives, already with few clocks.

**Theorem.** For a [priced timed game](priced-timed-games-with-constrained-price-bounde.md), the existence of a winning strategy
for Player 1 is undecidable for each of the following objectives:

1. $\mathrm{Reach}({\bowtie} K)$, for priced timed games with two or more clocks and arbitrary prices;
2. $\mathrm{BReach}(K, T)$, for priced timed games with five or more clocks and prices $0$ and $1$;
3. $\mathrm{RReach}(\eta)$, for priced timed games with three or more clocks and arbitrary prices.

Undecidability for $\mathrm{Reach}({\le} K)$ with two clocks and arbitrary price rates had been shown earlier; the source
extends it to the other comparison operators. The bounded-time case is notable because bounding time recovers decidability for many related problems.
For one-clock games whose location prices take only two values in $\{-1, 0, 1\}$, the source shows that the value of the
reachability-cost game is computable.

## Depends on

- [Priced timed games with constrained-price, bounded-time and repeated reachability objectives](priced-timed-games-with-constrained-price-bounde.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Each proof reduces the halting problem for two-counter machines: Player 1 simulates the machine by choosing delays that adjust the
clocks to the counter values, and Player 2 may interrupt and enter a checking widget whose accumulated price detects a wrong delay.
For $\mathrm{Reach}({=} 1)$ two clocks suffice: on entry to the module of an instruction, $x_1 = 1 / (5^{c_1} 7^{c_2})$ and $x_2 = 0$, where
$c_1, c_2$ are the counter values. For $\mathrm{BReach}(K, T)$ with five clocks, one of $x_1, x_2$ holds $1 / (2^{k + c_1} 3^{k + c_2})$
before the $(k+1)$-th instruction and a clock $z$ tracks the elapsed time $1 - 2^{-k}$, so the whole simulation fits in bounded time.
For $\mathrm{RReach}(\eta)$ three clocks encode $1 / (5^{c_1} 7^{c_2})$ as for the first case.

## Sources

- T. Brihaye, G. Geeraerts, S. N. Krishna, L. Manasa, B. Monmege and A. Trivedi, "Adding negative prices to priced timed games", in *CONCUR 2014 – Concurrency Theory*, Lecture Notes in Computer Science 8704, pp. 560–575, Springer, 2014, doi:10.1007/978-3-662-44584-6_38; numbering of the version arXiv:1404.5894v6: the first theorem of Section 3 (undecidability for the three objectives), its proof sketch in Section 4, and the decidability theorem for one-clock bi-valued games in Section 3.
