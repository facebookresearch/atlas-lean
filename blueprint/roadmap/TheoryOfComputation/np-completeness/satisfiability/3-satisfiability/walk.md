# One step of the clause-length walk

Write $w_0, w_1, w_2, w_3$ for the walking labels
after zero, one, two, and three or more literals of the current clause. For a Boolean cap flag
$\mathrm{cap}$ and a label $\ell$, the filter statement run at $\ell$: if the token stack is
empty, go to the label $\mathrm{back}$; if its top is the clause marker, move it onto the side
stack and go to $w_0$; if its top is a polarity marker, move it onto the side stack and go to
$w_1$, $w_2$, $w_3$ when $\ell$ is $w_0$, $w_1$, $w_2$ respectively, to $\mathrm{fail}$ when
$\ell = w_3$ and $\mathrm{cap}$ is true, and to $\ell$ otherwise; if its top is a name bit, move
it onto the side stack and stay at $\ell$; on any other symbol, go to $\mathrm{fail}$ without
moving it. Each test stores its outcome in the local variable.
