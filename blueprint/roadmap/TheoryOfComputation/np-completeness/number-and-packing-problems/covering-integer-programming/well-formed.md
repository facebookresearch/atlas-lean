# Well-formed COVERING INTEGER PROGRAMMING instances

An instance $(n, C, c, K)$ of COVERING INTEGER PROGRAMMING is well-formed when every row $A_i$ has $n$ entries in $[0, 1]$ (each with positive denominator), every $b_i = p/q$ has $q > 0$ and $p \ge q$ (so $b_i \ge 1$), $c$ has $n$ entries in $[0, 1]$ (each with positive denominator, so an entry with denominator $0$ is rejected rather than read as $0$), and $K > 0$.
