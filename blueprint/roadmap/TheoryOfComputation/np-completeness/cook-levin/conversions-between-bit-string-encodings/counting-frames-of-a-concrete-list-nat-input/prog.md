# Program of the frame counter for lists of naturals

The frame counter is a multi-stack Turing machine whose three [stacks](k.md) (input, scratch, count) hold bits,
with Boolean internal state and the [labels](lab.md) loop, block, bump, clear, good, bad. Its program is:

- At loop: if the input is nonempty go to block, otherwise go to good.
- At block: the [framed-pair reading step](../reading-a-framed-bit-block/read.md) from the input to the scratch
  stack (every symbol is a bit), staying at block after a payload pair, going to bump at the end of the block and to
  bad on malformed framing.
- At bump: push $1$ onto the counter and go to clear.
- At clear: pop the scratch stack if it is nonempty and stay at clear; if it is empty, go to loop.
- At good and bad: halt.
