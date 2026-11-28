# Deciding the winner of the two-player domino game on the plane is undecidable

In the two-player domino game, players alternately color cells of the grid, the first player trying to create a forbidden pattern and the
second to avoid one forever; deciding whether the first player wins on $\mathbb{Z}^d$, $d \ge 2$, is $\Sigma^0_1$-complete.

**The game.** Fix $d > 0$, a finite alphabet $\mathcal{A}$ and a finite set $\mathcal{F}$ of finite forbidden patterns, which together define a subshift of finite type on $\mathbb{Z}^d$ (an instance of the
domino problem, as for [Wang tiles](wang-tiles-and-valid-tilings.md)). In the *domino game* $\Gamma(\mathcal{A}, \mathcal{F}, \mathbb{Z}^d)$, the players $A$ and $B$ start from the empty pattern, with $A$ to move, and
alternate; a move either passes or colors one uncolored cell with a letter of $\mathcal{A}$. As soon as some pattern of $\mathcal{F}$ appears, the game ends and $A$ wins; $B$ wins if this never
happens. In the *non-alternating* game $\Gamma_s$ for a word $s \in \{A, B\}^\omega$, the player at turn $i$ is $s_i$ instead. A word $s$ is *balanced* if any two factors of the same length contain numbers
of $A$ that differ by at most $1$; then $A$ has a well-defined frequency $f_A(s)$ in $s$.

**Theorem.**

1. For every $d \ge 2$, it is $\Sigma^0_1$-complete, and in particular undecidable, given $(\mathcal{A}, \mathcal{F})$, whether $A$ has a winning strategy in $\Gamma(\mathcal{A}, \mathcal{F}, \mathbb{Z}^d)$.
2. For a balanced word $s$ and $d \ge 2$, if $0 < f_A(s) \le 1/2$ then the complement of the domino problem on $\mathbb{Z}^d$ reduces to deciding whether $A$ wins $\Gamma_s(\mathcal{A}, \mathcal{F}, \mathbb{Z}^d)$, so the latter is
   undecidable; otherwise it is decidable.

In contrast, whether $A$ can win within a given number $T$ of moves is decidable, even though each position has infinitely many moves.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [The arithmetical class $\Sigma_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

Membership in $\Sigma^0_1$ comes from compactness: $B$ wins on $\mathbb{Z}^d$ exactly when $B$ wins on every finite box, so a win of $A$ is witnessed on a finite box. For hardness, the complement of the
domino problem reduces to the game: from $(\mathcal{A}, \mathcal{F})$ one computes a new instance $(\mathcal{A}', \mathcal{F}')$, with pairs of letters, arrows and a fresh blocking symbol, such that $A$ wins its game exactly when
the subshift defined by $(\mathcal{A}, \mathcal{F})$ is empty. When $A$ moves more than half of the time in a balanced order, $A$ always wins on a nonempty $\mathcal{F}$ by building isolated copies of a forbidden pattern; when $A$
moves at most once the game is decided by bounded play.

## Sources

- B. Hellouin de Menibus and R. Pallen, "Two-player domino games", in *Twenty Years of Theoretical and Practical Synergies (CiE 2024)*, Lecture Notes in Computer Science 14773, pp. 139–152, Springer, 2024, doi:10.1007/978-3-031-64309-5_12; read in arXiv:2310.19759v2: Theorem 1 of Section 3 (Complexity of the Domino game problem) with Propositions 1 (membership) and 2 (hardness), Theorem 2 of Section 4 (Games with bounded time), and Theorem 3 (balanced turn orders) in Section 5 (Non-alternating play), with the numbering of that version.
