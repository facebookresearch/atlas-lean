# Smolensky's theorem: MOD_q is not in AC0[p]

For a natural number $m \ge 2$, the function $\mathrm{MOD}_m$ on $n$ bits is $0$ exactly when the number of ones is divisible by $m$. $\mathsf{ACC}^0(m)$, also written
$\mathsf{AC}^0[m]$, is the class of Boolean functions computed by families of circuits of constant depth and polynomial size with unbounded fan-in
AND, OR, NOT and $\mathrm{MOD}_m$ gates.

**Theorem (Razborov, Smolensky).** For distinct primes $p$ and $q$, $\mathrm{MOD}_p \notin \mathsf{ACC}^0(q)$.

For $p = 2$ and $q = 3$ the proof gives a quantitative bound. A depth-$h$ circuit with $\mathrm{MOD}_3$ gates and $S$ gates agrees with a polynomial over
$\mathbb{F}_3$ of degree $(2\ell)^h$ on all but an $S/2^\ell$ fraction of the inputs. No polynomial of degree $\sqrt n$ over $\mathbb{F}_3$ agrees with parity on more than
a $\frac{49}{50}$ fraction of the inputs. Taking $2\ell = n^{1/(2d)}$ for depth $d$, every depth-$d$ circuit with $\mathrm{MOD}_3$ gates computing parity on $n$ bits has
$2^{\Omega(n^{1/(2d)})}$ gates.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Section 13.2: Theorem 13.5 and its proof for parity versus $\mathsf{ACC}^0(3)$ (Steps 1 and 2).
