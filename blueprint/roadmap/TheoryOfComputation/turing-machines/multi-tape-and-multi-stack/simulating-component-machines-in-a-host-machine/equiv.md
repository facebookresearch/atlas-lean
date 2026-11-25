# Labels of the generic host as a sum type

For a component machine $c$ with labels $L$, let
$P_0$ be the set of phase-0 labels and $B = \{\mathrm{false}, \mathrm{true}\}$. The host labels of
$c$ are in bijection with the disjoint union $P_0 \sqcup L \sqcup B \sqcup B$: the phase-0 label
$p$ corresponds to $p$, the host copy of the component label $l$ to $l$, the cleanup label with
answer $a$ to $a$ in the first copy of $B$, and the output label with answer $a$ to $a$ in the
second copy of $B$.

The bijection shows that there are finitely many host labels.
