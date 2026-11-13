# The dense CNF-SAT verifier program

The program assigns a statement to each label. Every
pop stores the popped symbol, or nothing if the stack was empty, as the machine state.

* $\mathsf{read1}$: pop the input stack; while the popped symbol is some $\mathrm{inl}\,b$, push
  $\mathrm{inl}\,b$ onto $F$ and pop again; otherwise go to $\mathsf{read2}$.
* $\mathsf{read2}$: pop the input stack; while the popped symbol is some
  $\mathrm{inr}(\mathrm{some}\,b)$, push $\mathrm{inl}\,b$ onto $A$ and pop again; otherwise go
  to $\mathsf{back1}$.
* $\mathsf{back1}$: pop $F$ and push each popped symbol onto the input stack until $F$ is empty,
  then go to $\mathsf{back2}$.
* $\mathsf{back2}$: pop $A$ and push each popped symbol onto $B$ until $A$ is empty, then go to
  $\mathsf{c0}(\mathrm{false})$.
* $\mathsf{c0}(fl)$: pop the input stack; if the popped symbol is $\mathrm{inl}\,b$, go to
  $\mathsf{c1}(fl, b)$, otherwise go to $\mathsf{drainI}(\mathrm{true})$.
* $\mathsf{c1}(fl, \mathrm{false})$: pop the input stack; on $\mathrm{inl}\,\mathrm{false}$ go to
  $\mathsf{restore}(fl)$, on $\mathrm{inl}\,\mathrm{true}$ go to
  $\mathsf{adv}(fl, \mathrm{none})$, otherwise go to $\mathsf{drainI}(\mathrm{true})$.
* $\mathsf{c1}(fl, \mathrm{true})$: pop the input stack; on $\mathrm{inl}\,s$ go to
  $\mathsf{adv}(fl, \mathrm{some}\,s)$, otherwise go to $\mathsf{drainI}(\mathrm{true})$.
* $\mathsf{adv}(fl, o)$: pop $B$; if a symbol $x$ was popped, push $x$ onto $A$ and go to
  $\mathsf{c0}(fl')$, where $fl'$ is true when $fl$ is true, or when $o = \mathrm{some}\,s$ for a
  bit $s$ with $x = \mathrm{inl}(\lnot s)$; if $B$ was empty, go to $\mathsf{c0}(fl)$.
* $\mathsf{restore}(fl)$: pop $A$ and push each popped symbol onto $B$ until $A$ is empty, then
  go to $\mathsf{c0}(\mathrm{false})$ if $fl$ is true and to $\mathsf{drainI}(\mathrm{false})$
  otherwise.
* $\mathsf{drainI}(ans)$, $\mathsf{drainA}(ans)$, $\mathsf{drainB}(ans)$: pop and discard the
  input stack, $A$, $B$ respectively until it is empty, then go to $\mathsf{drainA}(ans)$,
  $\mathsf{drainB}(ans)$, $\mathsf{finish}(ans)$ respectively.
* $\mathsf{finish}(ans)$: push $ans$ onto the output stack, clear the machine state and halt.
