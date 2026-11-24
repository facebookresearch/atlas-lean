# Reading pair descriptions

Write a binary string $s$ as $1^n s'$, where $n$ is the number
of leading $1$s, and let $r$ be $s'$ without its first letter ($r$ is empty when $s'$ is). Let
$r_1$ be the first $\min(n, |r|)$ letters of $r$ and $r_2$ the remaining ones. The pair reader
maps $s$ to the concatenation $U(r_1)\,U(r_2)$, where $U$ is the universal description method,
and is undefined when $U(r_1)$ or $U(r_2)$ is undefined. On a pair description $1^n 0 r$ with
$|r| \ge n$, this is the concatenation of what the first $n$ letters of $r$ and the rest
describe.
