# Program of the number-pair projector

The number-pair projector is a multi-stack Turing machine whose six [stacks](k.md) hold bits, with Boolean internal
state and the [labels](lab.md) above. Its program is:

- At $\mathrm{pair}(\ell)$: the statement of the [pair-frame
  splitter](../raw-projection-of-the-canonical-pair-frame/prog.md) at $\ell$, transported along the [splitter stack
  embedding](pair-emb.md) and the [splitter label map](pair-label.md).
- At $\mathrm{norm}(s, \ell)$: the statement of the [payload
  normalizer](../a-linear-time-machine-for-total-binary-payload-n/prog.md) at $\ell$, transported along the [field
  stack embedding](norm-emb.md) and the [field label map](norm-label.md) for $s$.
- At good and bad: halt.
