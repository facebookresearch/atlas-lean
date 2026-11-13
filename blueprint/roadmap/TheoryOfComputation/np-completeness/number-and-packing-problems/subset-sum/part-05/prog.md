# The SUBSET-SUM verifier program

The program on the stacks $X, W, T, A, B, P, Q$ over
the verifier's symbols, with Boolean internal state, given label by label. A popped symbol that
is not a bit counts as false, as does a pop from an empty stack. Reading a pair of a block off
$X$ with flag $z$ ("the bits read so far end in false") goes to $\mathsf{no}$ if $X$ is empty;
on the end marker false it goes to $\mathsf{no}$ if $z$ holds and otherwise ends the block; on
true it reads a payload bit $b$, going to $\mathsf{no}$ if $X$ has ended.

* $\mathsf{tgt}(z)$: read a pair of the target block with flag $z$; at the end of the block go
  to $\mathsf{next}$; on a payload bit $b$, push $b$ onto $T$ and go to $\mathsf{tgt}(\lnot b)$.
* $\mathsf{next}$: if $X$ is empty go to $\mathsf{fmove}$; otherwise pop a witness bit $c$ off
  $W$ (false if absent) and go to $\mathsf{add}$ with carry false if $c$, else to
  $\mathsf{skip}$, with the flag unset.
* $\mathsf{add}(c, z)$: read a pair with flag $z$; at the end of the block go to
  $\mathsf{fin}(c)$; on a payload bit $b$, pop a bit $a$ off $A$ (false if absent), push
  $a \oplus b \oplus c$ onto $B$ and go to $\mathsf{add}(c', \lnot b)$, where $c'$ is the carry
  out of $a + b + c$.
* $\mathsf{skip}(z)$: read a pair with flag $z$; at the end of the block go to $\mathsf{next}$;
  on a payload bit $b$ go to $\mathsf{skip}(\lnot b)$.
* $\mathsf{fin}(c)$: carry $c$ through the rest of $A$, pushing the result bits onto $B$, then
  go to $\mathsf{back}$.
* $\mathsf{back}$: move the bits on top of $B$ onto $A$ one by one, then go to $\mathsf{next}$.
* $\mathsf{fmove}$: move the bits on top of $A$ onto $B$ one by one, then go to $\mathsf{cmp}$.
* $\mathsf{cmp}$: compare the bit blocks on top of $B$ and $T$, using $P$ and $Q$ as scratch, and
  go to $\mathsf{yes}$ if they are equal and to $\mathsf{no}$ otherwise.
* $\mathsf{yes}$ and $\mathsf{no}$: halt.
