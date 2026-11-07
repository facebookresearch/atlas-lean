# Time bound of the shift generator on the tables of a machine

Let $M$ be a finite
multi-stack Turing machine with window depth $d$, let $E$ be an encoding of $M$ with $A_0$
label/state codes and $N$ situations, and let $H \ge d$ and $T \in \mathbb{N}$. Run the cell-shift
generator for the layout of $E$, the table $\mathrm{sa}(i) = A_0 + i$ (the position of the
variable of situation $i$), the push counts $\mathrm{pl}$, the consumption counts $\mathrm{cn}$
and the pushed codes $\mathrm{pu}$ of $E$ and $N$ situations, started at its first precomputation
stage, in state false, with $T$ on the time counter and $H$ on the height counter in unary, all
other counters empty, and an arbitrary list $o$ of bits on the output stack. Then within
$c\,(T + H + 1)^6$ steps, where $c$ is the constant of the shift-generator time bound for this
layout and $N$, it reaches its final label $\mathsf{done}$, in some state, with stacks whose
output stack holds the encoding of the cell-shift clause family for this layout, $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$, $N$, $T$ and $H$, followed by $o$.
