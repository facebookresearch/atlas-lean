# Top-level substitution for beta reduction

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction). Let $\uparrow_c$ raises every variable index $k \ge c$ by one: $\uparrow_c \underline{k} = \underline{k}$ if $k < c$ and $\underline{k+1}$ otherwise, $\uparrow_c (t\,u) = (\uparrow_c t)(\uparrow_c u)$, $\uparrow_c (\lambda.\,t) = \lambda.\,\uparrow_{c+1} t$; let $\downarrow_c$ lowers every variable index $k > c$ by one: $\downarrow_c \underline{k} = \underline{k}$ if $k \le c$ and $\underline{k-1}$ otherwise, $\downarrow_c (t\,u) = (\downarrow_c t)(\downarrow_c u)$, $\downarrow_c (\lambda.\,t) = \lambda.\,\downarrow_{c+1} t$; and let $[c := s]$ replaces the variable $c$ by $s$: $[c := s]\underline{k} = s$ if $k = c$ and $\underline{k}$ otherwise, $[c := s]\,(t\,u) = ([c := s]t)([c := s]u)$, $[c := s]\,(\lambda.\,t) = \lambda.\,[c+1 := \uparrow_0 s]\,t$.

The top-level substitution of $s$ into the body $t$ of an abstraction is

$$t[s] = \downarrow_0 \bigl( [0 := \uparrow_0 s]\, t \bigr).$$

It shifts the argument up, substitutes it for the variable $\underline{0}$, and then lowers the remaining free indices for the removed binder. For example, $\underline{1}[\underline{0}] = \underline{0}$.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, §6.1.
