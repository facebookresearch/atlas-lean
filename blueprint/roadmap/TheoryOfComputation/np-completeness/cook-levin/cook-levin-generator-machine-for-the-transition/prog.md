# Generator machine for the transition clause families

Fix a layout $L$ with label/state
block size $A$, $K$ stacks and $g$ symbol codes, tables $\mathrm{la}$, $\mathrm{na}$,
$\mathrm{wa}$, and a number $N$ of situations, and let $n = Kd + 2$ be the number of literals of
a clause, where $d$ is the window depth. The generator is a multi-stack machine with a Boolean
output stack, the unit counters of the generator, and a Boolean internal state; below, moving a
counter onto targets means popping it until it is empty and pushing one unit onto every target
for each unit popped, and each multiplication uses $\mathsf{md}$ as its index counter and
$\mathsf{tmp}$ as scratch. Its precomputation pushes $g$ units on $\mathsf{Gc}$, adds
$\mathsf{Hs} \cdot \mathsf{Gc}$ to $\mathsf{HG}$, pushes $A$ units on $\mathsf{Wc}$, pushes $K$
units on $\mathsf{Ka}$, adds $\mathsf{Ka} \cdot \mathsf{HG}$ to $\mathsf{Wc}$, empties
$\mathsf{Ka}$, moves $\mathsf{Tn}$ onto $\mathsf{Ka}$ and $\mathsf{tmp}$ and then $\mathsf{tmp}$
onto $\mathsf{Tn}$, pushes one unit on $\mathsf{Ka}$, adds $\mathsf{Ka} \cdot \mathsf{Wc}$ to
$\mathsf{Vc}$, empties $\mathsf{Ka}$ and goes to the loop head. At the loop head it pops
$\mathsf{Tn}$; if a unit was popped it pushes a unit on $\mathsf{Ti}$, adds
$\mathsf{Tn} \cdot \mathsf{Wc}$ to $\mathsf{TW}$ and goes to the clause routine of situation
$N - 1$ (to the end of the time step if $N = 0$); if $\mathsf{Tn}$ was empty it moves
$\mathsf{Ti}$ onto $\mathsf{Tn}$ and goes to its final label, where it halts. The clause routine
of situation $i < N$ prepends $[\mathrm{false}, \mathrm{false}]$ to the output, moves
$\mathsf{Vc}$ onto $\mathsf{P}$ and $\mathsf{tmp}$ and then $\mathsf{tmp}$ onto $\mathsf{Vc}$,
runs the literal routines of situation $i$ for literals $n - 1, n - 2, \dots, 0$ in turn, drains
$\mathsf{P}$ while prepending $[\mathrm{false}, \mathrm{true}]$ to the output once per unit, and
goes to the clause routine of situation $i - 1$, or to the end of the time step if $i = 0$. At
the end of a time step it empties $\mathsf{TW}$ and returns to the loop head.

It is meant to be started with $T$ on $\mathsf{Tn}$, $H$ on $\mathsf{Hs}$ and every other
counter empty.
