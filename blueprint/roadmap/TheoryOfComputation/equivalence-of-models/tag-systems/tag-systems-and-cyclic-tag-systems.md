# Tag systems and cyclic tag systems

A *tag system* (with deletion number $2$) over a finite alphabet $\Gamma$ is given by an appendant $\alpha(a) \in \Gamma^*$ for each $a \in \Gamma$. It acts on a finite
tape $w \in \Gamma^*$: at each step it deletes the first two symbols and appends the appendant of the first one, so $abu \mapsto u\,\alpha(a)$; more
generally a tag system may delete a fixed number $p$ of symbols at each step, still reading only the first. A *cyclic tag system* is a
finite list of appendants $\beta_0, \dots, \beta_{m-1} \in \{Y, N\}^*$ acting on a tape over $\{Y, N\}$: at step $t$ it deletes the first symbol and, if
that symbol was $Y$, appends $\beta_{t \bmod m}$; then it moves on to the next appendant in the list, cyclically.

## Sources

- M. Cook, "Universality in elementary cellular automata", *Complex Systems* 15(1):1–40, 2004: Section 2.1 (tag systems, after E. Post, with footnote 2 on deleting $p$ symbols) and Section 2.2 (cyclic tag systems).
