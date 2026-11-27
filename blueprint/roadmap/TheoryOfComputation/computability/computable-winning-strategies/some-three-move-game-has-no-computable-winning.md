# Some three-move game has a winning strategy but no computable one

There is a game in which two players alternately choose three natural numbers, with a computable rule deciding the winner, such that the second player has a winning strategy but no computable winning strategy.

**Games.** For $m \ge 1$ and a computable function $W \colon \mathbb{N}^m \to \{\mathrm{A}, \mathrm{B}\}$, the game $G(m, W)$ is played by two players, A and B, who alternately choose natural numbers $x_1, x_2, \dots, x_m$, starting with A, with perfect information; the winner is $W(x_1, \dots, x_m)$. By the theorem of Zermelo, König and Kalmár, exactly one of the players has a winning strategy.

**Theorem (Rabin).** There is a computable $W \colon \mathbb{N}^3 \to \{\mathrm{A}, \mathrm{B}\}$ such that in the three-move game $G(3, W)$ player B has a winning strategy, but no computable winning strategy: there is no computable function $w \colon \mathbb{N} \to \mathbb{N}$ such that the move $x_2 = w(x_1)$ wins for B against every $x_1$ and $x_3$.

A computable winning condition does not make winning effective. The survey also notes that, given $m$ and $W$, it is undecidable which player has a winning strategy, already for one-move games.

## Depends on

None.

## Proof depends on

- [Post's theorem: simple sets exist](../halting-problem-and-rice-s-theorem/post-s-theorem-simple-sets-exist.md)

## Expansion

Fix a simple set $S \subseteq \mathbb{N}$, a computably enumerable set whose complement is infinite and contains no infinite computably enumerable set, and a computable $g$ with $g(\mathbb{N}) = S$. In the game, A wins exactly when $x_1 + x_2 = g(x_3)$. Player B wins by choosing $x_2 = t - x_1$ for some $t \notin S$ with $t > x_1$, which exists because the complement of $S$ is infinite. A computable winning strategy $w$ would make $\{x_1 + w(x_1) : x_1 \in \mathbb{N}\}$ an infinite computably enumerable subset of the complement of $S$, a contradiction.

## Sources

- M. O. Rabin, "Effective computability of winning strategies", in M. Dresher, A. W. Tucker and P. Wolfe (eds.), *Contributions to the Theory of Games, Volume III*, Annals of Mathematics Studies 39, Princeton University Press, 1957, pp. 147–157, doi:10.1515/9781400882151-008: the original result, cited beside the survey read below.
- B. Poonen, "Undecidable problems: a sampler", in J. Kennedy (ed.), *Interpreting Gödel: Critical Essays*, Cambridge University Press, 2014, pp. 211–241; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Theorem 14.2 and its proof, with the setting of Section 14.1 and Theorem 14.1 (which player wins is undecidable), in the numbering of that version.
