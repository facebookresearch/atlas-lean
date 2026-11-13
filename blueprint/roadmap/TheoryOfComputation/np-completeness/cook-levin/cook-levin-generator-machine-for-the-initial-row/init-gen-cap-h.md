# The init generator at the stack cap

Let $E$ be an encoding of a machine $M$ with window
depth $d$, let $x$ and $Y$ be lists of symbols of the input stack of $M$, let $m, T$ be natural
numbers with $|x| \le m$, let $H = m + (T + 1)d + 1$ be the stack cap, and let $o$ be a bit
string. Let $C$ be the time constant for the layout of $E$, the number of distinct codes of $Y$
and the number $k_0$ of the input stack. Start the generator for $E$ (start code: the code of
the pair of the main label and the initial state; stack $k_0$; code list: the distinct codes of
$Y$ in increasing order) at its start label with state false, with the counters $\mathrm{Tn},
\mathrm{Xn}, \mathrm{En}, \mathrm{Fn}$ holding $T$, $|x|$, $m - |x|$, $H - m$ in unary and all
other counters empty, $o$ on the output stack, and the list of codes of $x$, reversed, on the
input stack. Then within $C\,(T + H + 1)^5$ steps it reaches the final label $\mathrm{done}$,
and its output stack there is the bit encoding of the init family of $E$ for $x, Y, m, T, H$
followed by $o$.
