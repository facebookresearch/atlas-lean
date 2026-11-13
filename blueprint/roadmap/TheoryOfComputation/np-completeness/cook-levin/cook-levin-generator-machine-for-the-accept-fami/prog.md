# Generator machine for the accept family

Fix a layout $L$ with label/state block size
$A$, $K$ stacks and $g$ symbol codes, and naturals $n_1$, $a$, $k_1$, $e$. The generator is a
multi-stack machine with a Boolean output stack, the unit counters of the generator, and a
Boolean internal state. Its precomputation pushes $g$ units on $\mathsf{Gc}$, adds
$\mathsf{Hs} \cdot \mathsf{Gc}$ to $\mathsf{HG}$, pushes $A$ units on $\mathsf{Wc}$, pushes $K$
units on $\mathsf{Kc}$, adds $\mathsf{Kc} \cdot \mathsf{HG}$ to $\mathsf{Wc}$, adds
$\mathsf{Tn} \cdot \mathsf{Wc}$ to $\mathsf{TW}$, pushes one unit on $\mathsf{Tn}$, adds
$\mathsf{Tn} \cdot \mathsf{Wc}$ to $\mathsf{Vc}$, drains $\mathsf{TW}$ onto both $\mathsf{CB}$
and $\mathsf{tmp}$ and then $\mathsf{tmp}$ back onto $\mathsf{TW}$, pushes $A$ units on
$\mathsf{CB}$, pushes $k_1$ units on $\mathsf{K1}$, adds $\mathsf{K1} \cdot \mathsf{HG}$ to
$\mathsf{CB}$, and goes to the first clause label; each multiplication uses $\mathsf{md}$ as
its index counter and $\mathsf{tmp}$ as scratch. For each clause $c$ (a code clause of $u < n_1$
or a cell clause of $x < g$) it prepends $[\mathrm{false}, \mathrm{false}]$ to the output,
drains $\mathsf{Vc}$ onto both $\mathsf{P}$ and $\mathsf{tmp}$ and then $\mathsf{tmp}$ back onto
$\mathsf{Vc}$, runs the literal routine of $c$ with polarity parameters $a$ and $e$, drains
$\mathsf{P}$ while prepending $[\mathrm{false}, \mathrm{true}]$ to the output once per unit, and
goes to the label after $c$. At its final label it halts.

It is meant to be started with $T$ on $\mathsf{Tn}$, $H$ on $\mathsf{Hs}$ and every other
counter empty.
