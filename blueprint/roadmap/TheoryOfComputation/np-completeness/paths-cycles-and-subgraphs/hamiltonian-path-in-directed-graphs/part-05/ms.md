# Quiescent states of the HAMPATH emitter

A quiescent state consists of lists of token
symbols $t$, $f$, $v$, $w$, $g$, $x$ (meant as the token stack, the tokens in reading order, the
distinct variables, the other side of the variable walk, garbage, and the first comparison
scratch stack), a list of bits $o$ (the output stack), a list of bits $q$ (the edge bits so far,
in reading order), and natural numbers $c$, $c_3$, $p$, $n$, $r$, $l$, $j$, $d$ (meant as the
clause count, three times it, the diamond top, the row end, the row vertex, the row loop index,
the clause index and the detour vertex).

On the emitter's stacks such a state holds each counter as a unary stack of $\mathrm{cl}$ symbols
and the edge bits $q$ on $Q$ reversed, as name-bit symbols; the scratch stacks $Y$ and $Z$ are
empty, and $X$ is empty except while a new name is copied onto $V$.
