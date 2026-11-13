# No NTM accepts exactly the binary code of $0$

Let $m$ be a single-tape nondeterministic
Turing machine with tape alphabet $\Sigma$, and let $\iota$ be any map from the bits to $\Sigma$.
For a natural number $n$, write $w_n$ for the word over $\Sigma$ obtained by applying $\iota$
letter by letter to the little-endian binary code of $n$, in which $0$ is coded by the empty word.
Then it is not the case that, for every natural number $n$, $m$ accepts $w_n$ if and only if
$n = 0$.

The word $w_0$ is empty, and a machine that accepts the empty word accepts every word, in
particular $w_1$.
