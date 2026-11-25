# Walk step of the PATH marking machine

Given a counter stack $c$, a label $\ell$ and a
final statement $f$, the walk step pops the top of $c$. If $c$ was nonempty, it goes to $\ell$
after moving the top mark of the marks stack $M$, if there is one, onto the parked stack $P$:
the mark is popped, read as a bit (a symbol that is not a bit reads as false), and pushed on
$P$ as that bit. If $c$ was empty, it runs $f$.
