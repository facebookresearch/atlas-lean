# Feasible instances of SHIFT BRIBERY for Borda

An instance $(m, p, W, B)$ of SHIFT BRIBERY for Borda, where $W$ lists one pair $(v_i, P_i)$ of a vote and a price list per voter $i$, is feasible when there are natural numbers $k_i$, one per listed voter, such that:

- $k_i \le j_i$ for every voter $i$, where $j_i$ is the zero-based index of the first occurrence of $p$ in voter $i$'s vote $v_i$ (the length of $v_i$ if $p$ does not occur in it); thus a voter who ranks $p$ first allows no shift, and a voter who ranks $p$ third allows a shift of up to two places;
- the total [price](price.md) $\sum_i \rho_i(k_i)$, where $\rho_i$ is read from $P_i$, is at most $B$; and
- in the bribed election, in which voter $i$ casts its vote [with $p$ shifted up by $k_i$ places](shift.md), no candidate $d < m$ has a larger Borda score than $p$.

Feasibility does not include well-formedness; the decision problem requires both.
