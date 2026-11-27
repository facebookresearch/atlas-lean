# The universal description method

The universal description method $U$ is the partial function from binary strings to binary
strings defined as follows. If a binary string $p$ contains a $0$, write $p = 1^n 0 w$, where $n$
is the number of leading $1$s; then $U(p)$ is the result of [running](run.md) the code with
number $n$, in the standard numbering of codes for partial recursive functions, on $w$, and $U(p)$
is undefined when that run is. If $p$ contains no $0$ (a string of $1$s, the empty string
included), $U(p)$ is undefined.
