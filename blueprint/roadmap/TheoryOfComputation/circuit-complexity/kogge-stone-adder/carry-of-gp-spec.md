# Carries from the Kogge–Stone prefixes

Let $x, y$ be $n$-bit vectors, $c$ a carry-in bit,
and $K$, $i$ natural numbers with $n \le 2^K$ and $i < n$. Let $(G, P)$ be the generate and
propagate signals that bit $i$ holds after $K$ Kogge–Stone levels, those of the block of the at
most $2^K$ bits ending at bit $i$. Then the carry into bit $i + 1$ of $x + y + c$, which is true
exactly when $(x \bmod 2^{i+1}) + (y \bmod 2^{i+1}) + c \ge 2^{i+1}$, equals
$G \lor (P \land c)$.

Since $n \le 2^K$, that block is the whole prefix of bits $0, \dots, i$.
