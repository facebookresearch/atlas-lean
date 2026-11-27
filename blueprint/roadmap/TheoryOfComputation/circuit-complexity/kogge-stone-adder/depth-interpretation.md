# The depth interpretation

For a signature $\sigma$, the depth interpretation is the
interpretation of $\sigma$ in $\mathbb{N}$ that sends an operation symbol of arity $k$, applied to
argument depths $d_0, \dots, d_{k-1}$, to $\max(0, d_0, \dots, d_{k-1}) + 1$: a gate is one deeper
than its deepest argument, and a gate without arguments has depth $1$.
