# Index gadget and lifted search problems

A *search problem* on $n$ bits is a relation $R \subseteq \{0,1\}^n \times O$ (any $o$ with $(z, o) \in R$ is a correct answer on $z$). The *index gadget* $\mathrm{Ind}_m : [m] \times \{0,1\}^m \to \{0,1\}$ is $\mathrm{Ind}_m(a, w) = w_a$. The *lifted* problem $R \circ \mathrm{Ind}_m^n$ is the two-party search problem in which Alice holds pointers $x \in [m]^n$, Bob holds blocks $y \in (\{0,1\}^m)^n$, and they must output an answer to $R$ on the input $z = (y_{i}(x_i))_{i \in [n]}$. A decision tree for $R$ of depth $d$ yields a protocol for the lifted problem of cost $d(\lceil \log_2 m\rceil + 1)$: to query bit $i$, Alice sends $x_i$ and Bob replies with $y_i(x_i)$.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Deterministic Communication vs. Partition Number", SIAM Journal on Computing 47(6), 2018.
- R. Raz and P. McKenzie, "Separation of the Monotone NC Hierarchy", Combinatorica 19(3), 1999.
