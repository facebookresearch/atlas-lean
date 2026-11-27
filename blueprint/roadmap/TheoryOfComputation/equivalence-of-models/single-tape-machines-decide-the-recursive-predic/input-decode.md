# Input decoding

For a natural number $m > 0$, let $b_0, \dots, b_n$ be its binary
expansion, least significant bit first, without trailing zeros. The input decoding of $m$ is
$\sum_{i=0}^{n-1} b_{n-1-i} 2^i$, the value, least significant bit first, of the reversed
expansion with its first bit dropped. The input decoding of $0$, whose expansion is empty, is $0$.

It undoes the encoding of input words: for every natural number $k$ with binary expansion $w$,
least significant bit first, the input decoding of the number whose binary expansion, least
significant bit first, is the reversal of $w$ followed by $1$ is $k$.
