# Program of the payload normalizer machine

The payload normalizer is a multi-stack Turing machine whose three [stacks](k.md) (input, buffer, output) hold
bits, with Boolean internal state and the [labels](lab.md) $\mathrm{read}(\ell)$, copy and done. Its program is:

- At $\mathrm{read}(\ell)$: if the input stack is nonempty, pop its top bit $c$, push $c$ onto the buffer, set
  the internal state to $c$ and go to $\mathrm{read}(c)$. If the input stack is empty, set the internal state to
  $0$; then, if $\ell = 0$, push $1$ onto the buffer and go to copy, and otherwise go to copy directly.
- At copy: if the buffer is nonempty, pop its top bit, push it onto the output and go to copy; if the buffer is
  empty, go to done.
- At done: halt.

It uses only bit symbols and finitely many labels, and never computes the number its input denotes.
