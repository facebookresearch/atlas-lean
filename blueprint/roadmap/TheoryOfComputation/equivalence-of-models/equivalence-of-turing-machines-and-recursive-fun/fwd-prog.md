# The program of the wrapped machine

Let $c$ be a partial recursive code and let
$\mathrm{tr}$ be Mathlib's multi-stack machine that evaluates such codes, with stacks
$\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}$ and alphabet
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$. The program of the
wrapped machine for $c$ assigns a statement to each of its labels, namely the five adapter labels
$\mathrm{pre}_0, \mathrm{pre}_1, \mathrm{pre}_2, \mathrm{post}_1, \mathrm{post}_2$ and the labels
in Mathlib's finite support $\mathrm{supp}(c)$ of $\mathrm{tr}$ for $c$ with the halting
continuation. The internal state $v$ is a symbol of $\Gamma'$ or none, the input stack is the bit
stack $\mathrm{false}$ and the output stack is the bit stack $\mathrm{true}$.

At $\mathrm{pre}_0$: push $\mathtt{cons}$ onto $\mathrm{main}$ and go to $\mathrm{pre}_1$.

At $\mathrm{pre}_1$: pop the input stack and set $v$ to the popped bit as a symbol of $\Gamma'$
($\mathtt{bit1}$ for $\mathrm{true}$, $\mathtt{bit0}$ for $\mathrm{false}$), or to none if the
input stack is empty; if $v$ is a symbol, push it onto $\mathrm{rev}$ and go to $\mathrm{pre}_1$,
otherwise go to $\mathrm{pre}_2$.

At $\mathrm{pre}_2$: pop $\mathrm{rev}$ and set $v$ to the popped symbol (none if $\mathrm{rev}$
is empty); if $v$ is a symbol, push it onto $\mathrm{main}$ and go to $\mathrm{pre}_2$, otherwise
go to the start label of $\mathrm{tr}$ for $c$ with the halting continuation, which lies in
$\mathrm{supp}(c)$.

At a label $l \in \mathrm{supp}(c)$: execute the statement of $\mathrm{tr}$ at $l$, acting on the
stacks of $\mathrm{tr}$, where every jump of $\mathrm{tr}$ becomes a jump to the same label in
$\mathrm{supp}(c)$ and every halt becomes a jump to $\mathrm{post}_1$.

At $\mathrm{post}_1$: pop $\mathrm{main}$ and set $v$ to the popped symbol (none if
$\mathrm{main}$ is empty); if $v$ is none or $\mathtt{cons}$, go to $\mathrm{post}_2$, otherwise
push $v$ onto $\mathrm{rev}$ and go to $\mathrm{post}_1$.

At $\mathrm{post}_2$: pop $\mathrm{rev}$ and set $v$ to the popped symbol (none if $\mathrm{rev}$
is empty); if $v$ is a symbol, push onto the output stack the bit that is $\mathrm{true}$ if
$v = \mathtt{bit1}$ and $\mathrm{false}$ otherwise, and go to $\mathrm{post}_2$; otherwise halt.
