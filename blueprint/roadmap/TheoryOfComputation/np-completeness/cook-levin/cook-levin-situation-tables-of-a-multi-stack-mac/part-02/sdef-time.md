# Time bound of the situation-definition generator on the tables of a machine

Let $M$ be a
finite multi-stack Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$
label/state codes and $N$ situations, and let $H \ge d$ and $T \in \mathbb{N}$. Run the
transition-clause generator for the layout of $E$, the current-code table $\mathrm{la}$ of $E$,
the table $\mathrm{sa}(i) = A_0 + i$ (the position of the variable of situation $i$) in place of
the next-code table, the window table $\mathrm{wa}$ of $E$ and $N$ situations, started at its
first precomputation stage, in state false, with $T$ on the time counter and $H$ on the height
counter in unary, all other counters empty, and an arbitrary list $o$ of bits on the output
stack. Then within $c\,(T + H + 1)^5$ steps, where $c$ is the constant of the generator's time
bound for this layout and $N$, it reaches its final label $\mathsf{done}$, in some state, with
stacks whose output stack holds the encoding of the transition clause family for this layout,
$\mathrm{la}$, $\mathrm{sa}$, $\mathrm{wa}$, $T$, $H$ and $N$, followed by $o$.
