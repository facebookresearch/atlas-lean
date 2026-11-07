# The language of a side grammar

Let $\alpha$ be an alphabet with decidable equality,
let $P = (d_0, \dots, d_{k-1})$ be a list of dominoes over $\alpha$, let $\sigma$ assign a word
over $\alpha$ to each domino, and write $w_i = \sigma(d_i)$. A word $u$ over the letters of
$\alpha$ and the index terminals $0, 1, 2, \dots$ lies in the language of the side grammar of
$\sigma$ and $P$ if and only if there is a nonempty sequence of indices $i_1, \dots, i_n$, each
less than $k$, with $u = w_{i_1} \cdots w_{i_n} \, i_n \cdots i_1$.
