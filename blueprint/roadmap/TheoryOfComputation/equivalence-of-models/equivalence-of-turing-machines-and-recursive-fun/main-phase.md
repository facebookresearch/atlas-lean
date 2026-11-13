# Main phase of the wrapped machine

Let $c$ be a code and $f : \mathbb{N} \to \mathbb{N}$
such that $c$ evaluates to $[f(n)]$ on input $[n]$ for every $n$. Then for every $n$ there is
$N$ such that the wrapped machine, started at the label $\mathrm{trNormal}(c, \mathrm{halt})$ with
empty local state, the encoding $\mathrm{trList}([n])$ on the main stack and all other stacks
empty, is after exactly $N$ steps at the adapter label post1 with empty local state,
$\mathrm{trList}([f(n)])$ on the main stack and all other stacks empty.
