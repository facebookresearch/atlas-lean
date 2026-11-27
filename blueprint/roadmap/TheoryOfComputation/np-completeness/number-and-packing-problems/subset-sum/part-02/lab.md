# Labels of the subset-sum emitter

The control labels of the subset-sum emitter machine
are: $\mathrm{rdK}$, $\mathrm{rdN}$ and $\mathrm{mv}$ (parsing the two unary numbers $k$ and $n$
that open the input, and moving the pair bits); $\mathrm{tri}$, $\mathrm{triC}$,
$\mathrm{triC2}$, $\mathrm{cmp}$ and, for every ordering $o$, the labels $\mathrm{rc}(o)$ and
$\mathrm{rcB}(o)$ (counting the pairs and comparing that count with the number of pair bits);
$\mathrm{eg}$, $\mathrm{egX}$, $\mathrm{egR}$, $\mathrm{egR2}$ and $\mathrm{egY}$ (the edge
numbers); $\mathrm{vinit}$, $\mathrm{vtx}$, $\mathrm{pr}$, $\mathrm{rend}$, $\mathrm{rmv}$,
$\mathrm{vend}$, $\mathrm{vchk}$ and $\mathrm{rs}$ (the vertex numbers); $\mathrm{hv}$,
$\mathrm{hv0}$, $\mathrm{hv1}$ and $\mathrm{hvB}$ (the binary digits of $k$); $\mathrm{tem0}$,
$\mathrm{tsk}$ and $\mathrm{tem}$ (writing the target); $\mathrm{bad}$, which writes the fixed
no-instance; and the halting label $\mathrm{done}$.
