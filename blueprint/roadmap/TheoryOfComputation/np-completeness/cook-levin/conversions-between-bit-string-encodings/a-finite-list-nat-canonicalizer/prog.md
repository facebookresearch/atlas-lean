# Program of the list-of-naturals canonicalizer

The list canonicalizer is a multi-stack Turing machine whose six [stacks](k.md) hold bits, with Boolean internal
state and the [labels](lab.md) above. Its program is:

- At loop: if the input is nonempty go to block, otherwise go to finish.
- At block: the [framed-pair reading step](../reading-a-framed-bit-block/read.md) from the input to the workspace
  output stack (every symbol is a bit), staying at block after a payload pair, going to back at the end of the block
  and to bad on malformed framing. The payload lands reversed on the workspace output stack.
- At back: move the bits of the workspace output stack one by one onto the workspace input stack, staying at back;
  when the workspace output stack is empty, go to $\mathrm{nat}(\mathrm{read}(\text{none}))$. The payload now lies
  on the workspace input stack in its original order.
- At $\mathrm{nat}(\ell)$: the statement of the [payload normalizer](../a-linear-time-machine-for-total-binary-payload-n/prog.md)
  at $\ell$, acting on the workspace stacks through the [stack embedding](emb.md), with labels renamed by the
  [label map](nat-label.md) (its halting label done becomes emit).
- At emit: the [frame-emitting statement](../emitting-a-canonical-frame-in-reverse/emit-frame.md) from the workspace
  output stack to the accumulator, staying at emit and then going to loop.
- At finish: move the bits of the accumulator one by one onto the output, staying at finish; when the accumulator
  is empty, go to good.
- At good and bad: halt.
