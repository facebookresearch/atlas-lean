# Tail generated cells of a word

Let $Q$ and $\Gamma$ be sets. A cell tuple is a tuple $(a, x, s, f, \beta)$ as in a cell nonterminal. For a word $w = w_1 \cdots w_n$ over $\Gamma$, the tail generated cells of
$w$ form the empty list if $n = 0$, and otherwise the tuples $(w_j, w_j, \bot, 0, \mathrm{middle})$ for
$j < n$ followed by $(w_n, w_n, \bot, 0, \mathrm{right})$: inactive cells without the head, the last
tagged right and the others middle.
