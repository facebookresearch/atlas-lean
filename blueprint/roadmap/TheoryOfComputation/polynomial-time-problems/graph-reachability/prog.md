# The marking machine for PATH

The multi-stack machine program whose input lies on the
stack $X$ and whose answer is pushed on the Boolean stack $O$. To read a unary number off $X$ onto
a stack $d$, it pops a bit off $X$ and pushes it on $d$, repeating while the bit is true and
moving on after the first false bit; an empty $X$ jumps to `bad`. To walk along a counter $c$, it
pops units off $c$ one at a time, each time moving the top mark of $M$ (if there is one) onto $P$,
until $c$ is empty. To restore, it moves the bits on top of $P$ back onto $M$ one at a time.

At `rdS`, `rdT` and `rdN` it reads $s$, $t$ and $n$ in turn off $X$ onto $J$, pushing a counter
unit on $S$, $T$ or $N$ respectively for each true bit, and at `rdN` also a cleared mark on $M$;
then it goes to `val0`. At `val0` it goes to `goS` if $X$ is empty, and otherwise reads two unary
numbers off $X$ onto $E$ (at `valU` and `valV`) and returns to `val0`. At `goS` it walks along $S$
and then sets the top mark of $M$ (if any); at `backS` it restores and goes to `pass`. At `pass`
it pops a unit off $N$ and goes to `ld`, or to `goT` if $N$ is empty. At `ld` it moves the bits on
top of $E$ onto $X$, then goes to `edge`. At `edge` it goes to `pass` if $X$ is empty, and
otherwise reads $u$ and $v$ off $X$ onto $E$ (at `rdU` and `rdV`), pushing a counter unit on $U$,
respectively $V$, for each true bit, and then goes to `go1`. At `go1` it walks along $U$ and reads
the top mark $b$ of $M$ (false if there is none); at `back1 b` it restores and goes to `go2` if $b$
is true and to `drV` otherwise. At `go2` it walks along $V$ and sets the top mark of $M$ (if any);
at `back2` it restores and goes to `edge`. At `drV` it empties $V$ and goes to `edge`. At `goT` it
walks along $T$, pushes the top mark of $M$ (false if there is none) on $O$ and goes to `done`. At
`bad` it pushes false on $O$ and goes to `done`. At `done` it halts.
