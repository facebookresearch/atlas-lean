# Coloring an OR gadget

Read the colors $0, 1, 2$ as $T$, $F$ and $B$. For all
colors $c_a, c_o \in \{0, 1, 2\}$ with $c_a \ne 2$ and $c_o \ne 2$, there are colors
$c_u, c_v, c_w \in \{0, 1, 2\}$ with $c_a \ne c_u$, $c_o \ne c_v$, $c_u \ne c_v$,
$c_u \ne c_w$, $c_v \ne c_w$ and $c_w \ne 2$, such that $c_w = 0$ if and only if
$c_a = 0$ or $c_o = 0$.

These are the conditions for a proper coloring of an OR gadget with inputs $a, o$, fresh
vertices $u, v, w$ and edges $au$, $ov$, $uv$, $uw$, $vw$, $wB$, where $B$ has color $2$:
if both inputs are colored $T$ or $F$, the gadget can be colored so that its output $w$ is
$T$ or $F$, and $T$ exactly when some input is $T$.
