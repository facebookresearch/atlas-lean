# Program of the unary-to-binary converter

For a Boolean "framed", the unary-to-binary converter is a multi-stack Turing machine with the fifteen stacks of the
vertex-cover to subset-sum reduction machine ($O$ holds bits; $X$, $A$, $H$, $T$ and the others hold the reduction
machine's symbols), Boolean internal state and the [labels](lab.md) above. Its program is:

- At $\mathrm{emit}(\ell)$: the reduction machine's statement at $\ell$, with labels renamed by the [label
  map](emit-label.md). From label hv this phase halves the unary count on stack $A$ repeatedly, records the binary
  digits on $T$, and writes the framed binary code of the count onto $O$.
- At clean: pop each of the stacks $A$, $H$, $T$ that is nonempty and stay at clean; when all three are empty, go
  to done if framed is true and to read otherwise.
- At read: the [framed-pair reading step](../reading-a-framed-bit-block/read.md) from $O$ to $X$ (every symbol of
  $O$ is a bit, written on $X$ as a bit symbol), staying at read after a payload pair and going to back at the end
  of the block and to done on malformed framing.
- At back: move the bit symbols of $X$ one by one back onto $O$, staying at back; at the first symbol that is not a
  bit, or when $X$ is empty, go to done.
- At done: halt.

With framed true the converter leaves the new frame on $O$; with framed false it removes the frame and leaves only
the binary code, above any earlier contents of $O$.
