# Substitution for a de Bruijn variable

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction). Let $\uparrow_c$ raise every variable index $k \ge c$ by one: $\uparrow_c \underline{k} = \underline{k}$ if $k < c$ and $\underline{k+1}$ otherwise, $\uparrow_c (t\,u) = (\uparrow_c t)(\uparrow_c u)$, $\uparrow_c (\lambda.\,t) = \lambda.\,\uparrow_{c+1} t$.

For $c \in \mathbb{N}$ and a term $s$, the substitution $[c := s]$ replaces the variable $c$ by $s$: $[c := s]\underline{k} = s$ if $k = c$ and $\underline{k}$ otherwise, $[c := s]\,(t\,u) = ([c := s]t)([c := s]u)$, $[c := s]\,(\lambda.\,t) = \lambda.\,[c+1 := \uparrow_0 s]\,t$.

Variables other than $c$ are left unchanged; in particular, indices above $c$ are not decremented, so this operation alone does not remove a binder.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, §6.2, Def. 6.2.4.
