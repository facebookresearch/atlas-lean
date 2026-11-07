# Labels of the dense-SAT verifier

The labels of the verifier's program are
$\mathrm{read1}$, $\mathrm{read2}$, $\mathrm{back1}$ and $\mathrm{back2}$; $\mathrm{c0}(f)$ and
$\mathrm{c1}(f, b)$ for Booleans $f$ and $b$; $\mathrm{adv}(f, o)$ for a Boolean $f$ and an
optional Boolean $o$; $\mathrm{restore}(f)$ for a Boolean $f$; and $\mathrm{drainI}(a)$,
$\mathrm{drainA}(a)$, $\mathrm{drainB}(a)$ and $\mathrm{finish}(a)$ for a Boolean $a$. There are
finitely many labels, and equality of labels is decidable.

The labels $\mathrm{c0}(f)$ and $\mathrm{c1}(f, b)$ read the two bits of a token, with $f$
recording whether the current clause is already satisfied. $\mathrm{adv}(f, o)$ moves one
assignment bit from stack $B$ to stack $A$ ($o = \mathrm{some}\ s$ for the literal token $1s$),
and $\mathrm{restore}(f)$ moves the used assignment bits back from $A$ to $B$.
