# Program of the four-output pair-list decoder

The four-output decoder is a multi-stack Turing machine whose seventeen [stacks](k.md) hold bits, with Boolean
internal state and the [labels](lab.md) above. Its program is:

- At $\mathrm{split}(\ell)$: the statement of the [pair-frame
  splitter](../raw-projection-of-the-canonical-pair-frame/prog.md) at $\ell$, transported along the [splitter
  embedding](split-emb.md) and [splitter label map](split-label.md).
- At $\mathrm{items}(\ell)$: the statement of the [pair-list
  projector](../canonical-projection-of-lists-of-binary-nat-pair/prog.md) at $\ell$, transported along the
  [list-projector embedding](items-emb.md) and [label map](items-label.md).
- At $\mathrm{pair}(\ell)$: the statement of the [number-pair
  projector](../projecting-and-normalizing-a-pair-of-binary-natu/prog.md) at $\ell$, transported along the
  [pair-projector embedding](pair-emb.md) and [label map](pair-label.md).
- At good and bad: halt.

So it splits off the framed first field, projects the list of pairs it codes, and then normalizes the remaining
pair.
