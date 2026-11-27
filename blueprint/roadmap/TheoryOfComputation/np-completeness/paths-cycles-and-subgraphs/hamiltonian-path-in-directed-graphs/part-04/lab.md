# Labels of the HAMPATH emitter

Let $f$, $p_p$, $p_n$ and $b$ range over bits and $j$ over
copy sites. A label of the emitter is one of $\mathrm{a0}$, $\mathrm{anm}$, $\mathrm{aw}(f)$,
$\mathrm{ac}(f)$, $\mathrm{ar1}(f)$, $\mathrm{ar2}(f)$, $\mathrm{amv}(f)$, $\mathrm{asep}(f)$,
$\mathrm{ab}(f)$, $\mathrm{ad2}$, $\mathrm{ad3}$, $\mathrm{b0}$, $\mathrm{b1}$,
$\mathrm{h0}, \dots, \mathrm{h5}$, $\mathrm{r0}, \dots, \mathrm{r4}$, $\mathrm{wi}$,
$\mathrm{e0}$, $\mathrm{e1}$, $\mathrm{e2}$, $\mathrm{dw}(p_p, p_n)$, $\mathrm{dk}(p_p, p_n)$,
$\mathrm{dr1}(p_p, p_n, b)$, $\mathrm{dr2}(p_p, p_n, b)$, $\mathrm{dm}(p_p, p_n, b)$,
$\mathrm{dl}(p_p, p_n, b)$, $\mathrm{dj}$, $\mathrm{t0}, \dots, \mathrm{t8}$,
$\mathrm{z0}, \dots, \mathrm{z9}$, $\mathrm{cpA}(j, b)$, $\mathrm{cpB}(j, b)$,
$\mathrm{post}(j, b)$ and $\mathrm{done}$, all distinct.

Their roles, in terms of the emitter's stacks: in phase A, $\mathrm{a0}$ reads a token,
$\mathrm{anm}$ moves a name to $F$, and $\mathrm{aw}(f)$ to $\mathrm{asep}(f)$ walk $V$, with $f$
recording whether a match was found ($\mathrm{ac}$ compares, $\mathrm{ar1}$ and $\mathrm{ar2}$
restore, $\mathrm{amv}$ and $\mathrm{asep}$ move the entry to $W$); $\mathrm{ab}(f)$ moves $W$ back
(and, when no match was found, pushes a separator), and $\mathrm{ad2}$, $\mathrm{ad3}$ copy the
name onto $V$. For the diamonds, $\mathrm{b0}$, $\mathrm{b1}$ set $P$; $\mathrm{h0}$ takes the next
entry; $\mathrm{h1}$ to $\mathrm{h5}$ set $N$; $\mathrm{r0}$ to $\mathrm{r4}$ run the row loop, with
$\mathrm{wi}$ advancing $R$; $\mathrm{e0}$ to $\mathrm{e2}$ set $D$; $\mathrm{dw}(p_p, p_n)$ walks
$F$ with the clause flags, $\mathrm{dk}$, $\mathrm{dr1}$, $\mathrm{dr2}$, $\mathrm{dm}$,
$\mathrm{dl}$ handle a literal with match bit $b$, and $\mathrm{dj}$ ends a clause; $\mathrm{t0}$
moves $T$ back to $F$, and $\mathrm{t1}$ to $\mathrm{t8}$ drop the entry and advance $P$. The labels
$\mathrm{z0}$ to $\mathrm{z9}$ produce the output, and $\mathrm{cpA}(j, b)$, $\mathrm{cpB}(j, b)$,
$\mathrm{post}(j, b)$ copy site $j$, passing $b$ on.
