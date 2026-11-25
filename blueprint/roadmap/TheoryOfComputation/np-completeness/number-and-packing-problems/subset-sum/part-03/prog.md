# The subset-sum emitter machine

A multi-stack machine with the labels of the subset-sum
emitter as control labels, a Boolean internal state, and the stacks of the emitter: the output
stack $O$ holds bits, every other stack holds symbols. Stacks are read top first, $U$ is the
counter unit, and to prepend a list to $O$ is to push it so that it reads top first. The labels
act as follows.

$\mathrm{rdK}$: if $X$ is empty, go to $\mathrm{bad}$; otherwise pop $X$, and if the popped
symbol is $\mathrm{bit}(\mathrm{true})$ push $U$ on $A$ and repeat, else go to $\mathrm{rdN}$.
$\mathrm{rdN}$: the same, except that each $\mathrm{bit}(\mathrm{true})$ pushes $U$ on $N$ and
$\mathrm{val}(\mathrm{false})$ on $L$, and the other case goes to $\mathrm{mv}$. $\mathrm{mv}$: if
$X$ is empty, go to $\mathrm{tri}$; otherwise pop $X$, let $s$ say whether the popped symbol is
$\mathrm{bit}(\mathrm{true})$, push $\mathrm{val}(s)$ on $Y$, then $\mathrm{bit}(\mathrm{false})$
and $\mathrm{bit}(s)$ on $T$, then $U$ on $C$, and repeat.

$\mathrm{tri}$: pop $N$; if it was empty go to $\mathrm{cmp}$, else go to $\mathrm{triC}$, which
pops $N$ until it is empty, pushing $U$ on $M$ and on $S_1$ for each popped symbol, and then to
$\mathrm{triC2}$, which pops $S_1$ until it is empty, pushing $U$ on $N$ for each, and returns to
$\mathrm{tri}$. $\mathrm{cmp}$: pop $C$ and $M$ together, pushing $U$ on $S_1$ for each symbol
popped from $C$ and on $S_2$ for each symbol popped from $M$, until one of them was empty; go to
$\mathrm{rc}(o)$ where $o$ is $<$, $=$ or $>$ according as only $C$, both, or only $M$ was empty.
$\mathrm{rc}(o)$ pops $S_1$ until empty, pushing $U$ on $C$ for each, then $\mathrm{rcB}(o)$ pops
$S_2$ until empty, pushing $U$ on $M$ for each, then goes to $\mathrm{eg}$ if $o$ is $=$ and to
$\mathrm{bad}$ otherwise.

$\mathrm{eg}$: if $Y$ is empty, go to $\mathrm{egY}$; otherwise pop $Y$, let $s$ say whether the
popped symbol is $\mathrm{val}(\mathrm{true})$, push $\mathrm{val}(s)$ on $Z$, pop $C$ and $M$,
and if $s$ is true prepend $(\mathrm{true}, \mathrm{true}, \mathrm{false})$ to $O$ and go to
$\mathrm{egX}$, else prepend $(\mathrm{false})$ to $O$ and repeat. $\mathrm{egX}$ pops $C$ until
it is empty, prepending $(\mathrm{true}, \mathrm{false}, \mathrm{true}, \mathrm{false})$ to $O$
for each popped symbol; then $\mathrm{egR}$ pops $M$ until empty, pushing $U$ on $C$ and on $S_1$
for each, and $\mathrm{egR2}$ pops $S_1$ until empty, pushing $U$ on $M$ for each, and returns to
$\mathrm{eg}$. $\mathrm{egY}$: while the top of $Z$ is some $\mathrm{val}(b)$, pop it and push
$\mathrm{val}(b)$ on $Y$; then go to $\mathrm{vinit}$.

$\mathrm{vinit}$: pop $L$; if a symbol was popped, push $\mathrm{val}(\mathrm{true})$ on $L$ and
go to $\mathrm{vtx}$, else go to $\mathrm{hv}$. $\mathrm{vtx}$: prepend
$(\mathrm{true}, \mathrm{true}, \mathrm{false})$ to $O$ and go to $\mathrm{pr}$. $\mathrm{pr}$: if
$R$ is empty, go to $\mathrm{rend}$; otherwise pop $R$, let $m$ be true exactly when the popped
symbol is $\mathrm{val}(\mathrm{true})$ and push $\mathrm{val}(m)$ on $\mathrm{Rt}$, let $a$ be
true exactly when the top of $L$ is $\mathrm{val}(\mathrm{true})$, pop $Y$, let $b$ be true
exactly when a $\mathrm{val}(\mathrm{true})$ was popped and push $\mathrm{val}(b)$ on $Z$,
prepend $(\mathrm{true}, b \wedge (m \vee a), \mathrm{true}, \mathrm{false})$ to $O$, and repeat.
$\mathrm{rend}$: while the top of $\mathrm{Rt}$ is some $\mathrm{val}(b)$, pop it and push
$\mathrm{val}(b)$ on $R$; then go to $\mathrm{rmv}$. $\mathrm{rmv}$: pop $L$, push
$\mathrm{val}(t)$ on $R$ where $t$ is true exactly when a $\mathrm{val}(\mathrm{true})$ was
popped, and go to $\mathrm{vend}$ if $L$ is now empty, else to $\mathrm{pr}$. $\mathrm{vend}$:
while the top of $Z$ is some $\mathrm{val}(b)$, pop it and push $\mathrm{val}(b)$ on $Y$; then
go to $\mathrm{vchk}$. $\mathrm{vchk}$: go to $\mathrm{hv}$ if the top of $R$ is
$\mathrm{val}(\mathrm{true})$, else to $\mathrm{rs}$. $\mathrm{rs}$: if $R$ is empty, go to
$\mathrm{vtx}$; otherwise pop $R$; if the popped symbol is $\mathrm{val}(\mathrm{true})$, pop $L$
and push $\mathrm{val}(\mathrm{true})$ and then $\mathrm{val}(\mathrm{false})$ on $L$, else push
$\mathrm{val}(\mathrm{false})$ on $L$; repeat.

$\mathrm{hv}$: go to $\mathrm{tem0}$ if $A$ is empty, else to $\mathrm{hv0}$. $\mathrm{hv0}$: pop
$A$; if it was empty, push $\mathrm{bit}(\mathrm{false})$ on $T$ and go to $\mathrm{hvB}$, else go
to $\mathrm{hv1}$. $\mathrm{hv1}$: pop $A$; if it was empty, push $\mathrm{bit}(\mathrm{true})$
on $T$ and go to $\mathrm{hvB}$, else push $U$ on $H$ and go to $\mathrm{hv0}$. $\mathrm{hvB}$
pops $H$ until it is empty, pushing $U$ on $A$ for each, and returns to $\mathrm{hv}$.
$\mathrm{tem0}$: prepend $(\mathrm{false})$ to $O$ and go to $\mathrm{tsk}$. $\mathrm{tsk}$: if
$T$ is empty, go to $\mathrm{done}$; otherwise pop $T$, and if the popped symbol is
$\mathrm{bit}(\mathrm{true})$ prepend $(\mathrm{true}, \mathrm{true})$ to $O$ and go to
$\mathrm{tem}$, else repeat. $\mathrm{tem}$: if $T$ is empty, go to $\mathrm{done}$; otherwise pop
$T$, let $s$ say whether the popped symbol is $\mathrm{bit}(\mathrm{true})$, prepend
$(\mathrm{true}, s)$ to $O$, and repeat. $\mathrm{bad}$: prepend the encoding of the subset-sum
instance with no numbers and target $1$ to $O$ and go to $\mathrm{done}$. $\mathrm{done}$: halt.
