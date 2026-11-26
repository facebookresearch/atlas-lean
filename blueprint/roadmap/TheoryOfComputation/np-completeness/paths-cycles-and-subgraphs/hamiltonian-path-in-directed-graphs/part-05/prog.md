# The HAMPATH emitter machine

The emitter is the multi-stack machine with the emitter's
stacks (the output stack $O$ holds bits, every other stack holds token symbols), the emitter's
labels, and a boolean internal state. Below, *moving the bit block* of a stack $A$ onto a stack
$B$ means popping $A$ while its top is a name bit $\mathrm{bit}(b)$ and pushing each popped bit
onto $B$ (as $\mathrm{bit}(b)$, or as the bit $b$ when $B = O$). *Comparing* $F$ with $V$ means
popping both while their tops are equal name bits, pushing each such bit onto $X$ and onto $Y$,
and ending with "equal" if both bit blocks end together and with "different", without popping,
at the first mismatch. *Draining* $A$, pushing on given stacks, means popping $A$ until it is
empty and pushing on each of those stacks one symbol per popped symbol. Every pushed symbol not
otherwise named is the separator $\mathrm{cl}$. A list of steps written for several labels in
turn is done one label at a time, each label passing to the next.

Phase A. At $\mathrm{a0}$: if $T$ is empty, go to $\mathrm{b0}$; if its top is $\mathrm{cl}$, pop
it, push $\mathrm{cl}$ once on $F$, once on $C$ and three times on $M$, and go to $\mathrm{a0}$;
otherwise pop it, push on $F$ the polarity marker $\mathrm{lit}(s)$, where $s$ is true exactly
when the popped symbol is $\mathrm{lit}(\mathrm{true})$, and go to $\mathrm{anm}$. At
$\mathrm{anm}$: move the bit block of $T$ onto $F$, then go to $\mathrm{aw}(\mathrm{false})$. At
$\mathrm{aw}(f)$: go to $\mathrm{ab}(f)$ if $V$ is empty and to $\mathrm{ac}(f)$ otherwise. At
$\mathrm{ac}(f)$: compare $F$ with $V$, then go to $\mathrm{ar1}(\mathrm{true})$ if equal and to
$\mathrm{ar1}(f)$ if different. At $\mathrm{ar1}(f)$, $\mathrm{ar2}(f)$, $\mathrm{amv}(f)$ in
turn: move the bit block of $X$ onto $F$, of $Y$ onto $V$, and of $V$ onto $W$, then go to
$\mathrm{asep}(f)$. At $\mathrm{asep}(f)$: pop $V$, push $\mathrm{cl}$ on $W$ and go to
$\mathrm{aw}(f)$. At $\mathrm{ab}(f)$: if $W$ is empty, go to $\mathrm{a0}$ if $f$ is true, and
otherwise push $\mathrm{cl}$ on $V$ and go to $\mathrm{ad2}$; if the top of $W$ is $\mathrm{cl}$,
pop it and push $\mathrm{cl}$ on $V$; otherwise pop it and push $\mathrm{bit}(s)$ on $V$, where
$s$ is true exactly when the popped symbol is $\mathrm{bit}(\mathrm{true})$; in these last two
cases go to $\mathrm{ab}(f)$. At $\mathrm{ad2}$: move the bit block of $F$ onto $X$ and go to
$\mathrm{ad3}$. At $\mathrm{ad3}$: if the top of $X$ is a name bit, pop it, push it on $F$ and on
$V$ and go to $\mathrm{ad3}$; otherwise go to $\mathrm{a0}$.

Diamonds. At $\mathrm{b0}$, $\mathrm{b1}$ in turn: drain $C$ pushing on $P$ and $Z$, then drain
$Z$ pushing on $C$, then go to $\mathrm{h0}$. At $\mathrm{h0}$: go to $\mathrm{z0}$ if $V$ is empty
and to $\mathrm{h1}$ otherwise. At $\mathrm{h1}, \dots, \mathrm{h5}$ in turn: drain $P$ pushing on
$N$ and $Z$, drain $Z$ pushing on $P$, drain $M$ pushing on $N$ and $Z$, drain $Z$ pushing on
$M$, and push $\mathrm{cl}$ on $N$, then go to $\mathrm{cpA}(f_{1u}, \mathrm{false})$. At
$\mathrm{r0}$, $\mathrm{r1}$, $\mathrm{r2}$ in turn: drain $P$ pushing on $R$ and $Z$, drain $Z$
pushing on $P$, and push $\mathrm{cl}$ on $R$, then go to $\mathrm{r3}$. At $\mathrm{r3}$: if $M$
is empty go to $\mathrm{r4}$, and otherwise pop it, push $\mathrm{cl}$ on $L$ and go to
$\mathrm{cpA}(w_{1u}, \mathrm{false})$. At $\mathrm{r4}$: drain $L$ pushing on $M$ and go to
$\mathrm{e0}$. At $\mathrm{wi}$: push $\mathrm{cl}$ on $R$ and go to $\mathrm{r3}$. At
$\mathrm{e0}$, $\mathrm{e1}$, $\mathrm{e2}$ in turn: drain $P$ pushing on $D$ and $Z$, drain $Z$
pushing on $P$, and push $\mathrm{cl}$ twice on $D$, then go to
$\mathrm{dw}(\mathrm{false}, \mathrm{false})$.

Detours. At $\mathrm{dw}(p_p, p_n)$: if $F$ is empty go to $\mathrm{t0}$; if its top is
$\mathrm{cl}$, go to $\mathrm{cpA}(d_{1u}, p_n)$ if $p_p$ is true, else to
$\mathrm{cpA}(d_{3u}, \mathrm{false})$ if $p_n$ is true, else to $\mathrm{dj}$; otherwise go to
$\mathrm{dk}(p_p, p_n)$. At $\mathrm{dk}(p_p, p_n)$: compare $F$ with $V$, then go to
$\mathrm{dr1}(p_p, p_n, \mathrm{true})$ if equal and to $\mathrm{dr1}(p_p, p_n, \mathrm{false})$
if different. At $\mathrm{dr1}$, $\mathrm{dr2}$, $\mathrm{dm}$ with parameters $(p_p, p_n, b)$ in
turn: move the bit block of $X$ onto $F$, of $Y$ onto $V$, and of $F$ onto $T$, then go to
$\mathrm{dl}(p_p, p_n, b)$. At $\mathrm{dl}(p_p, p_n, b)$: pop $F$, push $\mathrm{lit}(s)$ on $T$,
where $s$ is true exactly when the popped symbol is $\mathrm{lit}(\mathrm{true})$, and go to
$\mathrm{dw}(p_p \lor (b \land s), p_n \lor (b \land \lnot s))$. At $\mathrm{dj}$: pop $F$, push
$\mathrm{cl}$ once on $T$, once on $J$ and three times on $D$, and go to
$\mathrm{dw}(\mathrm{false}, \mathrm{false})$. At $\mathrm{t0}$: if $T$ is empty go to
$\mathrm{t1}$; otherwise pop it, push on $F$ the symbol $\mathrm{cl}$ if the popped symbol is
$\mathrm{cl}$, $\mathrm{bit}(b)$ if it is $\mathrm{bit}(b)$, and otherwise $\mathrm{lit}(s)$ with
$s$ true exactly when it is $\mathrm{lit}(\mathrm{true})$, and go to $\mathrm{t0}$. At
$\mathrm{t1}, \dots, \mathrm{t8}$ in turn: move the bit block of $V$ onto $G$, pop $V$, drain $P$
pushing nothing, drain $N$ pushing on $P$, push $\mathrm{cl}$ on $P$, and drain $R$, $J$ and $D$
pushing nothing, then go to $\mathrm{h0}$.

Output. At $\mathrm{z0}$: move the bit block of $Q$ onto $O$ and go to $\mathrm{z1}$. At
$\mathrm{z1}, \dots, \mathrm{z9}$ in turn: push false and then true on $O$; drain $P$ pushing
true on $O$ and $\mathrm{cl}$ on $Z$; drain $Z$ pushing on $P$; push false on $O$; drain $P$
pushing true on $O$ and $\mathrm{cl}$ on $Z$; drain $Z$ pushing on $P$; push false on $O$; drain
$C$ pushing true on $O$ and $\mathrm{cl}$ on $Z$; and drain $Z$ pushing on $C$; then go to
$\mathrm{done}$. At $\mathrm{done}$: halt.

Copy sites. For a copy site $j$ and a bit $b$: at $\mathrm{cpA}(j, b)$, drain the stack of the
counter that $j$ reads, pushing $\mathrm{bit}(\mathrm{true})$ on $Q$ and $\mathrm{cl}$ on $Z$, and
go to $\mathrm{cpB}(j, b)$; at $\mathrm{cpB}(j, b)$, drain $Z$ pushing $\mathrm{cl}$ on the stack
of the counter that $j$ reads, and go to $\mathrm{post}(j, b)$; at $\mathrm{post}(j, b)$, in one
step push on $Q$ one $\mathrm{bit}(\mathrm{true})$ for each of the ones that $j$ adds to its
counter and then $\mathrm{bit}(\mathrm{false})$, and go to the label that follows $j$ for $b$.
