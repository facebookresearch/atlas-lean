# The dense-to-binary translation on the reversed bit string

The function
$\mathrm{conv}(w, \iota, n, k, m, o)$ consumes the bit string $w$ two bits at a time and prepends
to the output bit string $o$. The truth value $\iota$ records whether a clause is open, $n$ counts
the literals of the open clause, $k$ counts slots and $m$ counts clauses. Juxtaposition of bit
strings is concatenation, $1^n$ is $n$ ones, $(11)^k$ is $k$ copies of $11$, $\bar s$ is the
negation of a bit $s$, and $C$ is $1^n 0\, o$ if $\iota$ is true and $o$ otherwise. For every bit
$s$ and bit string $r$:

* $\mathrm{conv}(00\, r, \iota, n, k, m, o) = \mathrm{conv}(r, \mathrm{true}, 0, 0, m + 1, C)$;
* $\mathrm{conv}(10\, r, \iota, n, k, m, o) = \mathrm{conv}(r, \iota, n, k + 1, m, o)$;
* $\mathrm{conv}(s1\, r, \iota, n, k, m, o)$ is
  $\mathrm{conv}(r, \mathrm{true}, n + 1, k + 1, m, (11)^k 0 \bar s\, o)$ if $\iota$ is true and
  $\mathrm{conv}(r, \mathrm{false}, n, k, m, o)$ otherwise;
* if $w$ has fewer than two bits, $\mathrm{conv}(w, \iota, n, k, m, o) = 1^m 0\, C$.

On the reversed dense encoding a slot $s_1 s_2$ is read as $s_2 s_1$: $00$ is a terminator, which
closes the open clause and opens the next, $10$ is an absent slot, and $s1$ is a present slot,
whose literal $(2^k - 1, \bar s)$ is emitted (its binary code is $(11)^k 0 \bar s$) inside a
clause and skipped outside one. At the end the open clause is closed and the unary clause count
is emitted.
