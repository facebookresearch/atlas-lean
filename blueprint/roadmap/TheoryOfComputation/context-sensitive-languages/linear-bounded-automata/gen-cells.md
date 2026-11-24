# Generated cells of a word

Let $M$ be a linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$. A cell tuple is a tuple $(a, x, s, f, \beta)$ as in a cell nonterminal. For a word $w = w_0 \cdots w_{n-1}$ over $\Gamma$, the generated cells of $w$ form the empty
list if $n = 0$, the single tuple $(w_0, w_0, q_0, 0, \mathrm{both})$ if $n = 1$, and otherwise the
tuple $(w_0, w_0, q_0, 0, \mathrm{left})$ followed by $(w_j, w_j, \bot, 0, \mathrm{middle})$ for
$0 < j < n - 1$ and by $(w_{n-1}, w_{n-1}, \bot, 0, \mathrm{right})$, where $q_0$ is the initial state
of $M$. All cells are inactive and only the first carries the head.
