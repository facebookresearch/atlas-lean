# The marking machine for PATH

The multi-stack machine program whose input lies on the
stack $X$ and whose answer is pushed on the Boolean stack $O$. To read a unary number off $X$ onto
a stack $d$, it pops a bit off $X$ and pushes it on $d$, repeating while the bit is true and
moving on after the first false bit; an empty $X$ jumps to $\mathsf{bad}$. To walk along a counter $c$, it
pops units off $c$ one at a time, each time moving the top mark of $M$ (if there is one) onto $P$,
until $c$ is empty. To restore, it moves the bits on top of $P$ back onto $M$ one at a time.

At $\mathsf{rdS}$, $\mathsf{rdT}$ and $\mathsf{rdN}$ it reads $s$, $t$ and $n$ in turn off $X$ onto $J$, pushing a counter
unit on $S$, $T$ or $N$ respectively for each true bit, and at $\mathsf{rdN}$ also a cleared mark on $M$;
then it goes to $\mathsf{val0}$. At $\mathsf{val0}$ it goes to $\mathsf{goS}$ if $X$ is empty, and otherwise reads two unary
numbers off $X$ onto $E$ (at $\mathsf{valU}$ and $\mathsf{valV}$) and returns to $\mathsf{val0}$. At $\mathsf{goS}$ it walks along $S$
and then sets the top mark of $M$ (if any); at $\mathsf{backS}$ it restores and goes to $\mathsf{pass}$. At $\mathsf{pass}$
it pops a unit off $N$ and goes to $\mathsf{ld}$, or to $\mathsf{goT}$ if $N$ is empty. At $\mathsf{ld}$ it moves the bits on
top of $E$ onto $X$, then goes to $\mathsf{edge}$. At $\mathsf{edge}$ it goes to $\mathsf{pass}$ if $X$ is empty, and
otherwise reads $u$ and $v$ off $X$ onto $E$ (at $\mathsf{rdU}$ and $\mathsf{rdV}$), pushing a counter unit on $U$,
respectively $V$, for each true bit, and then goes to $\mathsf{go1}$. At $\mathsf{go1}$ it walks along $U$ and reads
the top mark $b$ of $M$ (false if there is none); at $\mathsf{back1}(b)$ it restores and goes to $\mathsf{go2}$ if $b$
is true and to $\mathsf{drV}$ otherwise. At $\mathsf{go2}$ it walks along $V$ and sets the top mark of $M$ (if any);
at $\mathsf{back2}$ it restores and goes to $\mathsf{edge}$. At $\mathsf{drV}$ it empties $V$ and goes to $\mathsf{edge}$. At $\mathsf{goT}$ it
walks along $T$, pushes the top mark of $M$ (false if there is none) on $O$ and goes to $\mathsf{done}$. At
$\mathsf{bad}$ it pushes false on $O$ and goes to $\mathsf{done}$. At $\mathsf{done}$ it halts.
