# Labels of the PATH marking machine

For an instance with source $s$, target $t$, $n$
vertices and arcs $(u, v)$, the labels of the PATH marking machine are $\mathsf{rdS}$,
$\mathsf{rdT}$ and $\mathsf{rdN}$ (read $s$, $t$ and $n$); $\mathsf{val0}$, $\mathsf{valU}$ and
$\mathsf{valV}$ (validate the edge list: at a pair, inside $u$, inside $v$); $\mathsf{goS}$ and
$\mathsf{backS}$ (walk to $s$ and set its mark, then restore); $\mathsf{pass}$ (the pass loop),
$\mathsf{ld}$ (reload the edges) and $\mathsf{edge}$ (the edge loop); $\mathsf{rdU}$ and
$\mathsf{rdV}$ (read $u$ and $v$); $\mathsf{go1}$ and, for each bit $b$, $\mathsf{back1}(b)$
(walk to $u$, then restore holding its mark $b$); $\mathsf{go2}$ and $\mathsf{back2}$ (walk to
$v$ and set its mark, then restore); $\mathsf{drV}$ (drain the counter stack $V$);
$\mathsf{goT}$ (walk to $t$ and answer); $\mathsf{bad}$ (answer false); and $\mathsf{done}$
(halt).
