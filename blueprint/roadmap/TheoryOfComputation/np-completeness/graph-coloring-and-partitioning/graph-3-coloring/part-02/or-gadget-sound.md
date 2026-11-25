# Soundness of the OR gadget

Read the colors $0, 1, 2$ as $T$, $F$ and $B$. If
colors $c_a, c_o, c_u, c_v, c_w \in \{0, 1, 2\}$ satisfy $c_a \ne 2$, $c_o \ne 2$,
$c_a \ne c_u$, $c_o \ne c_v$, $c_u \ne c_v$, $c_u \ne c_w$, $c_v \ne c_w$ and $c_w = 0$,
then $c_a = 0$ or $c_o = 0$.

That is, in a proper coloring of an OR gadget with inputs $a, o$, fresh vertices $u, v, w$
and edges $au$, $ov$, $uv$, $uw$, $vw$, if both inputs are colored $T$ or $F$ and the
output $w$ is $T$, then some input is $T$.
