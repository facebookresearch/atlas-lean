# Every rewrite preserves the invariant of reachable words

Let $M$ be a single-tape machine
with finite tape alphabet and finite set of states, and let $l$ be an input word. Write $\vdash$
and $\dashv$ for the left and right end markers and $H$ for the halting symbol. A word $w$
satisfies the invariant for $M$ and $l$ when either $w$ spells a configuration that $M$ reaches from
its initial configuration on $l$ (the configuration with state $q$, head symbol $h$, left part $L$
and right part $R$, finite words of tape symbols read from left to right beyond which the tape is
blank, is spelled ${\vdash}\,L\,q\,h\,R\,{\dashv}$), or $M$ halts on $l$ and
$w = {\vdash}\,X\,H\,Y\,{\dashv}$ for words $X$ and $Y$ of tape symbols. If $w$ satisfies the
invariant and rewrites in one step to $w'$ under the rules of $M$, then $w'$ satisfies the
invariant.
