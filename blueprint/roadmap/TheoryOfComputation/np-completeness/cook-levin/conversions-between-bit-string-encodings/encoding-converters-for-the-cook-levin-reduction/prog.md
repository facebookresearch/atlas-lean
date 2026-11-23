# Program of the converter to the canonical pair encoding

The machine has an input stack
of symbols, each a left-tagged bit, a right-tagged bit or the separator, and three stacks of
bits: the output and two stashes. Its program first pops input symbols and pushes the bit of
each left-tagged one onto the first stash, until the input is empty or the symbol popped is not
a left-tagged bit. It then pops input symbols and pushes the bit of each right-tagged one onto
the second stash, until the input is empty or the symbol popped is not a right-tagged bit. Next
it pops each bit $b$ of the second stash and pushes false, $b$, true onto the output, and then
pushes a single false. Finally it pops each bit $b$ of the first stash and pushes false, true,
$b$, true, true, true onto the output, and halts when the first stash is empty.

Each output block is pushed in reverse, so that it reads true, $b$, false (respectively true,
true, true, $b$, true, false) from the top.
