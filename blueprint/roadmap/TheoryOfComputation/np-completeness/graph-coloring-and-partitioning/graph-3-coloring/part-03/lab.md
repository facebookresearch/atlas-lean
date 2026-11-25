# Control labels of the 3-coloring emitter

The labels of the 3-coloring emitter, with their roles: $\mathsf{init}$ (write the palette);
$\mathsf{cls}$ (next clause); $\mathsf{lits}$ (next literal); $\mathsf{lp}$ and $\mathsf{nm}$ (pop
the polarity and the name); the walk labels $\mathsf{walk}$, $\mathsf{cmp}$, $\mathsf{rsA}(e)$
and $\mathsf{rsD}(e)$ for each bit $e$, $\mathsf{sel}$, $\mathsf{mvN}(r)$ for $r$ a bit or
nothing, $\mathsf{skU}$, $\mathsf{mvU}(b)$ for each bit $b$, and $\mathsf{dr}$ (walk the stack
$D$: compare, restore, select the polarity case, move the name and the vertex to $E$, or the
vertex to $U$ and push the consistency edges); $\mathsf{back}$ (move $E$ back to $D$);
$\mathsf{putN}$, $\mathsf{putW}$, $\mathsf{putA}$, $\mathsf{putB}$ and $\mathsf{putP}$ (put the
occurrence on $D$); $\mathsf{aft}$ and $\mathsf{fA}(b)$, $\mathsf{fB}(b)$, $\mathsf{fC}(b)$ for each
bit $b$ (set $R$ and advance $N$); $\mathsf{clr}(b)$ for each bit $b$ (clear $R$); $\mathsf{zN}$
(advance $N$ after an empty clause); $\mathsf{pre}(j)$, $\mathsf{cpA}(j)$ and $\mathsf{cpB}(j)$ for
each copy site $j$ (copy site $j$); and $\mathsf{done}$ (halt).
