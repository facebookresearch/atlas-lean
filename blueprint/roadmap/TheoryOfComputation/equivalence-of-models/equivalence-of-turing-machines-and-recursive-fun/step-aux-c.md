# The coded execution of a statement

This mirrors the machine's execution of one statement
on stacks of symbol codes. Given a statement $q$, an internal state $v$ and coded stacks $S$ (a list
$S_k$ of natural numbers for each stack index $k$), it returns a coded configuration (an optional
label, an internal state and coded stacks), by recursion on $q$. A push of $f$ onto stack $k$
followed by $q'$ replaces $S_k$ by the code of the symbol $f(v)$ of stack $k$ followed by $S_k$, and
continues with $q'$. A peek at stack $k$ with update $f$ followed by $q'$ continues with $q'$ from
the internal state $f(v, t)$, where $t$ is the top of coded stack $k$ as read from $S$. A pop is
the same as a peek but also removes the first entry of $S_k$ (if there is one). A load of $a$
followed by $q'$ continues with $q'$ from the internal state $a(v)$. A branch on $f$ executes its
first statement if $f(v)$ is true and its second otherwise. A goto $f$ stops with label $f(v)$,
internal state $v$ and stacks $S$, and a halt stops with no label, internal state $v$ and stacks
$S$.
