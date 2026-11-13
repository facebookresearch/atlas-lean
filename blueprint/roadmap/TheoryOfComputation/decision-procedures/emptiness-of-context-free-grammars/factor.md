# Factor of a word

For a word $w = w_0 w_1 \cdots w_{n-1}$ and natural numbers $i$ and
$j$, the factor of $w$ from position $i$ to position $j$ is obtained by dropping the first $i$
letters of $w$ and keeping at most the first $j - i$ letters of the rest, where $j - i$ is $0$
when $j \le i$. For $i \le j \le n$ it is $w_i w_{i+1} \cdots w_{j-1}$.
