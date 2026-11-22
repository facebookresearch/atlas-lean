# Cells of a pushed prefix over a truncated stack

Let $e$ map elements of $\alpha$ to natural
numbers, and for a list $L$ over $\alpha$ and $i \in \mathbb{N}$ let $L\langle i\rangle$ be $e$ of
the entry of $L$ at position $i$ (counting from $0$), or $0$ if $L$ has at most $i$ entries.
Subtraction of natural numbers is truncated at $0$. Let $P$ and $S$ be lists over $\alpha$ and
$n, H, d, j \in \mathbb{N}$ with $|P| \le d$, $n \le d$ and $|S| \le H - d$, and let $Q$ be $P$
followed by $S$ with its first $n$ entries removed. If $j < |P|$ then
$Q\langle j\rangle = P\langle j\rangle$; otherwise, if $j < (H - \max(|P|, n)) + |P|$ then
$Q\langle j\rangle = S\langle j - |P| + n\rangle$; and otherwise $Q\langle j\rangle = 0$.
