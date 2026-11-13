# Every clause of the Cook–Levin formula has one slot per variable

Let $E$ be an encoding
of a machine $M$, let $x$ and $Y$ be lists of input symbols of $M$, let $a$ be a symbol of its
output stack, and let $m, T \in \mathbb{N}$. Put $H = m + (T + 1)d + 1$, where $d$ is the window
depth of $M$. Then every clause of the Cook–Levin formula $\Phi(E, x, Y, a, m, T)$ is a dense
clause of length $(T + 1)(A + K H g)$, the number of variables of the layout of $E$ at time bound
$T$ and height $H$, where $A$, $K$ and $g$ are the label/state block size, the number of stacks
and the number of symbol codes of that layout.
