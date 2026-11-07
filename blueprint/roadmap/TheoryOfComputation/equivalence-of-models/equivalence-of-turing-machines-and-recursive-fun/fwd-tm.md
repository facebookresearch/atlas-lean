# The wrapped machine of a code

Let $c$ be a code for a partial recursive function on lists
of natural numbers, and let $\mathrm{tr}$ be Mathlib's multi-stack machine that evaluates such
codes, with stacks $K' = \{\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}\}$ and
alphabet $\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$. The
wrapped machine of $c$ is the finite multi-stack machine whose stacks are indexed by
$K' \sqcup \{\mathrm{false}, \mathrm{true}\}$, with alphabet $\Gamma'$ on each stack in $K'$ and
the alphabet of bits on the stacks $\mathrm{false}$ and $\mathrm{true}$; its input stack is
$\mathrm{false}$ and its output stack is $\mathrm{true}$; its labels are the labels of the
wrapped machine for $c$, with main label the first pre-phase adapter label $\mathrm{pre}_0$;
its internal states are the optional symbols of $\Gamma'$ (a symbol of $\Gamma'$, or none), with
initial state none; and its program is the program of the wrapped machine for $c$.
