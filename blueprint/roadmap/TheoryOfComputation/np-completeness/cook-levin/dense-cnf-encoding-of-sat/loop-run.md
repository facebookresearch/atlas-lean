# Running the generic copy loop of the dense-SAT verifier

Let $s$ be a work stack, $g$ a
partial map on the work alphabet $G$, $t$ an optional target work stack other than $s$, and
$\ell$, $\ell'$ labels such that the verifier's program at $\ell$ is the generic loop with source
$s$, map $g$, target $t$, own label $\ell$ and exit $\ell'$. Let $o$ be a list of output bits.
Let $x = x_1 \dots x_n$, $y = y_1 \dots y_n$ and $r$ be lists of symbols of $G$ with
$g(x_j) = y_j$ defined for every $j$, and with $r$ empty or $g$ undefined at the first symbol of
$r$. Let $V$ be work-stack contents with $V(s) = x r$, and let $v$ be any state. Started at
$\ell$ in state $v$ with work stacks $V$ and output stack $o$, the program runs for exactly
$n + 1$ steps and reaches the label $\ell'$. Its state is then the first symbol of $r$ (nothing
if $r$ is empty) and its output stack is still $o$. Its work stacks are obtained from $V$ by
replacing stack $s$ with $r$ minus its first symbol (empty if $r$ is empty) and then, if $t$ is
a stack, pushing $y_1, \dots, y_n$ onto $t$ one at a time.
