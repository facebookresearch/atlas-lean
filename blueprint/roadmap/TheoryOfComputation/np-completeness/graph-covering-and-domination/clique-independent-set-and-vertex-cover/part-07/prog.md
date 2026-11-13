# The KG-map machine

For a mode $m$ (flip or vc), the KG-map machine $M_m$ is the
multi-stack machine with stacks $X$, $A$, $B$, $D$, $Y$ of symbols and an output stack $O$ of
bits, whose labels act as follows; the counters $A$, $B$, $D$ use a fixed unit symbol.

- Read $k$: if $X$ is empty, go to the failure label. Otherwise pop $X$; if the popped symbol is
  the input bit $\mathrm{bit}(\mathit{true})$, push a unit onto $A$ and repeat, else go to read $n$.
- Read $n$: if $X$ is empty, go to the failure label. Otherwise pop $X$; if the popped symbol is
  $\mathrm{bit}(\mathit{true})$, push a unit onto $B$ and onto $D$ and repeat, else go to move.
- Move: if $X$ is empty, go to output pair bits (flip) or subtract (vc). Otherwise pop $X$, push
  $\mathrm{val}(b)$ onto $Y$, where $b$ is true exactly when the popped symbol was
  $\mathrm{bit}(\mathit{true})$, and repeat.
- Subtract: pop $A$. If $A$ was empty, go to output pair bits. Otherwise pop $D$; if $D$ was
  nonempty repeat, else go to the failure label.
- Output pair bits: if $Y$ is empty, push false onto $O$ and go to output $n$. Otherwise pop $Y$,
  push $\beta_m(b)$ onto $O$, where $b$ is true exactly when the popped symbol was
  $\mathrm{val}(\mathit{true})$ and $\beta_m$ is negation for flip and the identity for vc, and
  repeat.
- Output $n$: pop $B$; if $B$ was nonempty, push true onto $O$ and repeat, else go to separator.
- Separator: push false onto $O$ and go to output last number.
- Output last number: as output $n$, but popping the counter of $m$ ($A$ for flip, $D$ for vc)
  and going to the halting label when it is empty.
- Failure: push the bits true, false, false of the fixed no-instance (the encoding of $k = 1$ on
  the empty graph) onto $O$ so that $O$ starts with them, and go to the halting label.
- Halting label: halt.
