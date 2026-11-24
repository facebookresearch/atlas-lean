# Shannon: most Boolean functions need exponential circuits

For every natural number
$n \ge 10$, at least $2^{2^n}/2$ of the Boolean functions $f$ on $n$ input bits have the
following property: for every well-formed flat Boolean circuit $C$ on $n$ inputs without mod
gates whose wire count (the total length of the predecessor lists of its gates) is at most
$\lfloor 2^n / (10 n) \rfloor$, there is an input $x \in \{0,1\}^n$ such that $C$ has no
gates or the value of the last gate of $C$ on $x$ differs from $f(x)$.

## Sources

- C. E. Shannon, "The synthesis of two-terminal switching circuits", Bell System Technical Journal 28 (1949), 59-98.
