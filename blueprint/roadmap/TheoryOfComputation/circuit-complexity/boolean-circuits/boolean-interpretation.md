# Boolean interpretation

The Boolean interpretation evaluates the gates of the Boolean
signature on the truth values $\{\mathrm{false}, \mathrm{true}\}$: NOT sends its input $x$ to
$\lnot x$, and for each natural number $a$, the AND gate and the OR gate with inputs
$x_0, \dots, x_a$ return $(\cdots((\mathrm{true} \land x_0) \land x_1) \cdots) \land x_a$ and
$(\cdots((\mathrm{false} \lor x_0) \lor x_1) \cdots) \lor x_a$ respectively, that is, the
conjunction and the disjunction of the inputs.
