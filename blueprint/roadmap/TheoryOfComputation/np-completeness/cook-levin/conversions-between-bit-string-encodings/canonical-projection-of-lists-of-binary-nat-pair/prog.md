# Program of the pair-list projector

The pair-list projector is a multi-stack Turing machine whose eleven [stacks](k.md) hold bits, with Boolean internal
state and the [labels](lab.md) above. Its program is:

- At loop: if the input is nonempty go to block, otherwise go to $\mathrm{finish}(\text{first})$.
- At block: the [framed-pair reading step](../reading-a-framed-bit-block/read.md) from the input to the workspace's
  splitter scratch stack (every symbol is a bit), staying at block after a payload pair, going to back at the end of
  the block and to bad on malformed framing.
- At back: move the bits of the splitter scratch stack one by one onto the splitter input stack, staying at back;
  when it is empty, go to $\mathrm{pair}(\mathrm{pair}(\mathrm{read}))$.
- At $\mathrm{pair}(\ell)$: the statement of the [number-pair
  projector](../projecting-and-normalizing-a-pair-of-binary-natu/prog.md) at $\ell$, transported along the [stack
  embedding](pair-emb.md) and the [label map](pair-label.md).
- At $\mathrm{emit}(s)$: the [frame-emitting statement](../emitting-a-canonical-frame-in-reverse/emit-frame.md) from
  the workspace's left output (if $s$ is first) or right output (if $s$ is second) to accumulator $s$, staying at
  $\mathrm{emit}(s)$ and then going to $\mathrm{emit}(\text{second})$ if $s$ is first and to loop if $s$ is second.
- At $\mathrm{finish}(s)$: move the bits of accumulator $s$ one by one onto output $s$, staying at
  $\mathrm{finish}(s)$; when the accumulator is empty, go to $\mathrm{finish}(\text{second})$ if $s$ is first and to
  good if $s$ is second.
- At good and bad: halt.
