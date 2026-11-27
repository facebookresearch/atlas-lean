# Shifting de Bruijn indices down

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction).

For a cutoff $c \in \mathbb{N}$, the down-shift $\downarrow_c$ lowers every variable index $k > c$ by one: $\downarrow_c \underline{k} = \underline{k}$ if $k \le c$ and $\underline{k-1}$ otherwise, $\downarrow_c (t\,u) = (\downarrow_c t)(\downarrow_c u)$, $\downarrow_c (\lambda.\,t) = \lambda.\,\downarrow_{c+1} t$.

On variables with index above the cutoff it undoes the up-shift; variables with index at most $c$ are unchanged. It differs from the signed shift by $d = -1$, which would change every index $k \ge c$, including $k = c$.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, §§6.2–6.3.
