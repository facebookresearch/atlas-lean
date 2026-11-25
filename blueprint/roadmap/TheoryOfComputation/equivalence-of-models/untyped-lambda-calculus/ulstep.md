# One-step beta reduction

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction). For a term $s$ and an abstraction body $t$, let $t[s] = \downarrow_0 ([0 := \uparrow_0 s]\, t)$ be the top-level substitution (shift $s$ up, substitute it for $\underline{0}$, shift the result down).

One-step beta reduction $\to_\beta$ is the smallest relation on terms such that

- $(\lambda.\, t)\, u \to_\beta t[u]$;
- if $t \to_\beta t'$, then $t\,u \to_\beta t'\,u$;
- if $u \to_\beta u'$, then $t\,u \to_\beta t\,u'$;
- if $t \to_\beta t'$, then $\lambda.\, t \to_\beta \lambda.\, t'$.

## Sources

- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland, 1984, §3.1.
