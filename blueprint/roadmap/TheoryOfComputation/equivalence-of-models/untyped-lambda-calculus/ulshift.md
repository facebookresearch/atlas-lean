# Shifting de Bruijn indices up

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction).

For a cutoff $c \in \mathbb{N}$, the up-shift $\uparrow_c$ raises every variable index $k \ge c$ by one: $\uparrow_c \underline{k} = \underline{k}$ if $k < c$ and $\underline{k+1}$ otherwise, $\uparrow_c (t\,u) = (\uparrow_c t)(\uparrow_c u)$, $\uparrow_c (\lambda.\,t) = \lambda.\,\uparrow_{c+1} t$.

Thus $\uparrow_c$ adds one to the indices of the variables that are free relative to the cutoff, and leaves bound ones unchanged.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, §6.2, Def. 6.2.1, with shift amount $1$.
