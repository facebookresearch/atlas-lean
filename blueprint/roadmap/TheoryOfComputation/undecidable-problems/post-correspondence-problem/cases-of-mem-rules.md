# The eight kinds of rules of the machine-simulating rewriting system

Let $M$ be a
single-tape Turing machine with a finite tape alphabet $\Gamma$, a default (blank) symbol
$\beta \in \Gamma$ and finitely many states. The symbols are the tape symbols, the states, the end
markers $\vdash$ and $\dashv$, and the halting symbol $H$. Every rule $l \to r$ of the rewriting
system simulating $M$ has one of the following eight forms, where $q, q'$ are states and
$a, b, c$ are tape symbols. Either $M$ has no transition in state $q$ reading $a$, and $l = q\,a$,
$r = H$; or in state $q$ reading $a$ the machine $M$ goes to state $q'$ and writes $b$, and
$l = q\,a$, $r = q'\,b$; or in state $q$ reading $a$ it goes to $q'$ and moves the head right, and
either $l = q\,a \dashv$, $r = a\,q'\,\beta \dashv$ or $l = q\,a\,c$, $r = a\,q'\,c$; or in state
$q$ reading $a$ it goes to $q'$ and moves the head left, and either $l = \vdash q\,a$,
$r = \vdash q'\,\beta\,a$ or $l = c\,q\,a$, $r = q'\,c\,a$; or $l = c\,H$, $r = H$; or $l = H\,c$,
$r = H$.
