# Prepending a constant list

For a stack $k$, a list $(y_1, \dots, y_m)$ of symbols of
stack $k$ and a label $\ell$, this statement pushes $y_m, \dots, y_1$ onto stack $k$ in this order
and then goes to label $\ell$; it is the constant-list push of the reversed list. Afterwards
$y_1, \dots, y_m$ sit on top of stack $k$, read from the top down.
