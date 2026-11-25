# Correctness of Zielonka's recursive solver

Let $G$ be an encoded parity game on positions $\{0, \dots, n-1\}$, with an owner in $\{\text{even}, \text{odd}\}$, a Boolean move relation and a priority $\Omega(v) \in \mathbb{N}$ for each position, and write $Z(U) = (Z_1(U), Z_2(U))$ for the output of the Zielonka solver on a set $U$ of positions. For a nonempty $U$ let

- $d = \max_{v \in U} \Omega(v)$, and $p$ the player whose parity is that of $d$ (odd if $d$ is odd, even otherwise);
- $M = \{ v \in U : \Omega(v) = d \}$ and $A$ the attractor of $M$ for $p$ inside $U$;
- $U' = U \setminus A$, $W' = Z(U')$, and $\mathrm{Opp}$ the opponent's component of $W'$ (the even one if $p$ is odd, the odd one if $p$ is even);
- $B$ the attractor of $\mathrm{Opp}$ for the opponent inside $U$, $U'' = U \setminus B$ and $W'' = Z(U'')$.

Here the attractor of $T$ for a player inside $U$ is the $n$-fold iterate from $\emptyset$ of $X \mapsto (T \cap U) \cup \mathrm{CPre}(X)$, where $\mathrm{CPre}(X)$ consists of the positions of $U$ owned by that player with a move into $U \cap X$, together with the positions of $U$ owned by the other player all of whose moves into $U$ land in $X$.

Statement: the Zielonka solver $Z$ has all of the following properties.

1. For all $G$ and $U$: $Z_1(U) \subseteq U$ and $Z_2(U) \subseteq U$.
2. For all $G$ and $U$: $Z_1(U) \cup Z_2(U) = U$ and $Z_1(U) \cap Z_2(U) = \emptyset$.
3. For all $G$ and nonempty $U$: $U' \subsetneq U$; if $\mathrm{Opp} \neq \emptyset$ then $U'' \subsetneq U$; if $\mathrm{Opp} = \emptyset$ then $p$ wins all of $U$, that is $Z(U) = (\emptyset, U)$ when $p$ is odd and $Z(U) = (U, \emptyset)$ when $p$ is even; and if $\mathrm{Opp} \neq \emptyset$ then $Z(U)$ is $W''$ with $B$ added to the opponent's component.
4. For every $G$ in which every position has at least one move, and every position $v$: $v \in Z_1(\text{all positions})$ if and only if the even player has a winning positional strategy from $v$ in the associated parity game, and $v \in Z_2(\text{all positions})$ if and only if the odd player has one, with plays won under the max-parity condition.

## Sources

- W. Zielonka, "Infinite games on finitely coloured graphs with applications to automata on infinite trees", Theoretical Computer Science 200 (1998), 135-183 (the recursive solver and its correctness).
