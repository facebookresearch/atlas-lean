# One step to rejection

Let $\ell$ be a label, $v$ a bit and $S$ an assignment of symbol
stacks to the tokenizer's stacks. If executing the tokenizer's instruction at $\ell$ from internal
bit $v$ and stacks $S$ yields a configuration with label $\mathsf{rej}$, then the tokenizer
reaches $\mathsf{rej}$ within one step from the configuration with label $\ell$, internal bit $v$
and stacks $S$.
