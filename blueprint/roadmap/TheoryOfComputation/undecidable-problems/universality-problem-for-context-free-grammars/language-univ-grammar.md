# The language of the universality grammar

Let $\alpha$ be a finite alphabet with decidable
equality, let $P$ be a list of dominoes over $\alpha$ of length $m$, and for $i < m$ let $t_i$ and
$b_i$ be the top and bottom words of the domino of $P$ at position $i$, counting from $0$. Read the
bit $\mathrm{true}$ as the separator $|$ and the bit $\mathrm{false}$ as $1$, and let $c(i)$ be the
unary code of $i$: the bit $|$ followed by $i$ bits $1$. The language of the universality grammar
of $P$ equals the intended language of its start nonterminal $0$: a word over
$\alpha \oplus \mathrm{Bool}$ belongs to it exactly when at least one of the following holds: it
consists of letters from $\alpha$ only (possibly none); it is a word of letters followed by a
nonempty word of bits whose first bit is $1$; some bit is immediately followed by a letter; it
contains $c(m)$ as a contiguous factor; or it equals $x\, c(i_n) \cdots c(i_1)$ for a word $x$
over $\alpha$ and indices $i_1, \dots, i_n < m$ with $n \ge 1$ such that
$x \ne t_{i_1} \cdots t_{i_n}$ or $x \ne b_{i_1} \cdots b_{i_n}$.
