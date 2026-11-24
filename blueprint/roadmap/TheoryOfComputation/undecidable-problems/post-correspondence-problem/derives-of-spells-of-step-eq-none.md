# A halted configuration rewrites to the halting word

Let $M$ be a single-tape Turing
machine with finitely many states and tape symbols, and let $\vdash$, $\dashv$ be the end markers
and $H$ the halting symbol of the rewriting system simulating $M$. Let $c$ be a configuration of
$M$ at which $M$ has no next step, and let $w$ be a word that spells $c$: for some state $q$, tape
symbol $h$ and lists $L$, $R$ of tape symbols, $c$ is in state $q$ with $h$ under the head, the
tape left of the head reads $L$ from left to right and the tape right of the head reads $R$, up to
blanks at the far ends, and $w = \vdash L\,q\,h\,R \dashv$. Then $w$ rewrites in zero or more steps
of this rewriting system to the halting word $\vdash H \dashv$.
