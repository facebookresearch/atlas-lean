# A single-tape machine halts iff its start word rewrites to the halting word

Let $M$ be a
single-tape machine with finite tape alphabet and finite set of states, and write $\vdash$ and
$\dashv$ for the left and right end markers and $H$ for the halting symbol. For every input word
$l$, $M$ halts on $l$ if and only if the start word ${\vdash}\,q_0\,h\,R\,{\dashv}$ of $l$
rewrites to the halting word ${\vdash}\,H\,{\dashv}$ in zero or more steps under the rules of $M$,
where $q_0$ is the default state, $h$ is the first letter of $l$ (the blank if $l$ is empty) and
$R$ is the rest of $l$.
