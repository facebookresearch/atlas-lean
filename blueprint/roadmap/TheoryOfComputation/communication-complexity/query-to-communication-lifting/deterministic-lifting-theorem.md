# Raz–McKenzie / Göös–Pitassi–Watson deterministic lifting theorem

Let $R$ be a search problem on $n$ bits and let $m$ satisfy $\sqrt{m} \ge 320\, n^2 (\lfloor \log_2 m \rfloor + 1)$ (some $m = O(n^4 \log^2 n)$ suffices). If the lifted problem $R \circ \mathrm{Ind}_m^n$ has a deterministic protocol of cost $c$, then $R$ has a decision tree of depth $d$ with $d \log_2 m \le 4c$. Together with the trivial simulation,

$$D^{cc}\big(R \circ \mathrm{Ind}_m^n\big) = \Theta\big(D^{dt}(R) \cdot \log m\big).$$

## Proof sketch

The decision tree walks down the protocol maintaining a rectangle $X \times Y$ and a set of fixed coordinates such that $X$ is dense on the free coordinates and $Y$ has small deficiency. When Alice speaks, keep the larger half and restore density by the density-restoring partition, querying the newly fixed coordinates; when Bob speaks, keep the larger half. Each query costs $\Omega(\log m)$ bits of communication in a volume argument, and at a leaf the full-range lemma shows the answer is correct for every input consistent with the queries.

## Depends on

- [Index gadget and lifted search problems](index-gadget-and-lifted-search-problems.md)
- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Proof depends on

- [Full-range lemma for dense pointer sets](full-range-lemma.md)
- [Density-restoring partition](density-restoring-partition.md)

## Sources

- R. Raz and P. McKenzie, "Separation of the Monotone NC Hierarchy", Combinatorica 19(3), 1999.
- M. Göös, T. Pitassi and T. Watson, "Deterministic Communication vs. Partition Number", SIAM Journal on Computing 47(6), 2018.
- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020.
