# Periodicity lemma of Fine and Wilf

A word that has two periods $p$ and $q$ and length at least $p + q - \gcd(p, q)$ also has the period $\gcd(p, q)$.

For a list $w$ over a type $\alpha$ and a natural number $p$, say that $w$ has period $p$ if $w$ is a prefix of the list obtained by putting the prefix of $w$ of length $p$ in front of $w$; equivalently, $w_i = w_{i+p}$ for every index $i$ with $i + p < |w|$. If $w$ has periods $p$ and $q$ and

$$
p + q - \gcd(p, q) \le |w| ,
$$

then $w$ has period $\gcd(p, q)$, where $\gcd(0, q) = q$.

## Sources

- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: [List.HasPeriod.gcd](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/List/PeriodicityLemma.lean#L184 "List.HasPeriod.gcd"), with the definition [List.HasPeriod](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Data/List/PeriodicityLemma.lean#L41 "List.HasPeriod") and its index characterisation `List.hasPeriod_iff_getElem?`.
- N. J. Fine and H. S. Wilf, "Uniqueness theorems for periodic functions", Proceedings of the American Mathematical Society 16 (1965), 109–114, https://doi.org/10.1090/S0002-9939-1965-0174934-9.
