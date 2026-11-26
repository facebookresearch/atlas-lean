# Program of the raw pair-frame splitter

The pair-frame splitter is a multi-stack Turing machine whose three [stacks](k.md) (input, left, scratch) hold bits,
with Boolean internal state and the [labels](lab.md) read, copy, good, bad. Its program is:

- At read: the [framed-pair reading step](../reading-a-framed-bit-block/read.md) from the input to the scratch
  stack (every symbol is a bit), staying at read after a payload pair, going to copy at the end of the block and to
  bad on malformed framing.
- At copy: move the bits of the scratch stack one by one onto the stack left, staying at copy; when the scratch
  stack is empty, go to good.
- At good and bad: halt.
