# The pair walk lists the vertex pairs in reverse

Let $f$ be a function from the natural
numbers to the booleans, let $n$ be a natural number, and let $W$ be the pair walk. For every
$i \le n$, let $L$ be the list $f(i - 1), \dots, f(1), f(0)$ (empty when $i = 0$) and $R$ the
list $f(i), f(i + 1), \dots, f(n - 1)$ (empty when $i = n$). Then $W(L, R)$ is obtained as
follows: list the pairs $(a, j)$ of natural numbers with $a < i$ and $a < j < n$, with $a$
ascending and, for each $a$, $j$ descending; reverse this list; and replace each pair $(a, j)$
by $(f(a), f(j))$.
