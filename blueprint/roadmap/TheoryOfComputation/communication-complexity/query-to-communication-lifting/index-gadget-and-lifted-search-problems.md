# Index gadget and lifted search problems

A *search problem* on $n$ bits is a relation $R \subseteq \{0,1\}^n \times O$ that has a correct answer on every input: for every $z \in \{0,1\}^n$ the set $R(z) = \{o : (z, o) \in R\}$ is nonempty (any $o \in R(z)$ is a correct answer on $z$). A *promise* search problem instead fixes a domain $Z \subseteq \{0,1\}^n$ with $R(z) \ne \varnothing$ for $z \in Z$, and only inputs in $Z$ count; its lifted promise is the preimage of $Z$ under $\mathrm{Ind}_m^n$. The *index gadget* $\mathrm{Ind}_m : [m] \times \{0,1\}^m \to \{0,1\}$ is $\mathrm{Ind}_m(a, w) = w_a$. The *lifted* problem $R \circ \mathrm{Ind}_m^n$ is the two-party search problem in which Alice holds pointers $x \in [m]^n$, Bob holds blocks $y \in (\{0,1\}^m)^n$, and they must output an element of $R(z)$ for $z = \mathrm{Ind}_m^n(x, y) = (y_{i}(x_i))_{i \in [n]}$. Composition with an arbitrary gadget is defined in the same way on [Composed functions, gadgets and lifting theorems](../randomized-and-dag-like-lifting/composed-function-lifting.md). A decision tree for $R$ of depth $d$ yields a protocol for the lifted problem of cost $d(\lceil \log_2 m\rceil + 1)$: to query bit $i$, Alice sends $x_i$ and Bob replies with $y_i(x_i)$.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Composed functions, gadgets and lifting theorems](../randomized-and-dag-like-lifting/composed-function-lifting.md)

## Sources

- M. Göös, T. Pitassi and T. Watson, "Deterministic Communication vs. Partition Number", SIAM Journal on Computing 47(6), 2018.
- R. Raz and P. McKenzie, "Separation of the Monotone NC Hierarchy", Combinatorica 19(3), 1999.
- S. Lovett, R. Meka, I. Mertz, T. Pitassi and J. Zhang, "Lifting with Sunflowers", ITCS 2022 (search problems with an answer on every input).
