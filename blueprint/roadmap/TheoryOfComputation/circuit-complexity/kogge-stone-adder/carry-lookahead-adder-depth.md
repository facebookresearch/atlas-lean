# Exact depth of the carry-lookahead adder

For all $K \ge 1$ and $n \ge 2$, the $n$-bit
Kogge-Stone carry-lookahead adder with $K$ levels has depth exactly $2K + 3$, the depth being the
largest depth of an output with the inputs at depth $0$.

With $K = \lfloor \log_2 n \rfloor + 1$ levels this is $2 \lfloor \log_2 n \rfloor + 5$,
logarithmic in $n$, while the depth of the ripple-carry adder grows linearly in $n$.
