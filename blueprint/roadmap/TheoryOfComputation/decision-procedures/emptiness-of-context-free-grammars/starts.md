# Start positions of a right-hand side

Write $\langle s, t \rangle$ for the pairing
bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ given by $\langle s, t \rangle = t^2 + s$
if $s < t$ and $\langle s, t \rangle = s^2 + s + t$ otherwise. Given a word $w$, a list $R$ of
items (natural numbers), a position $j$ and an encoded right-hand side $X_1 \cdots X_m$, a
position $i$ is a start when there are positions $i = p_0, p_1, \ldots, p_m = j$ with
$p_0, \ldots, p_{m-1} \le |w|$ such that for each $l = 1, \ldots, m$: if $X_l$ is a terminal
$a$, then $p_l = p_{l-1} + 1$ and the letter of $w$ at position $p_{l-1}$ (counting from $0$)
is $a$; if $X_l$ is a nonterminal $B$, then $R$ contains the code
$\langle B, \langle p_{l-1}, p_l \rangle \rangle$. The starts are computed from the right, one
symbol at a time, by the symbol-fitting test; for the empty right-hand side the only start is
$j$.
