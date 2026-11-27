# Embedded number-pair projector preserves outside stacks

Let $M$ be a multi-stack Turing machine with Boolean internal state, stacks $J$ and labels $L$, and suppose it
contains the [number-pair projector](prog.md) through a stack embedding $E$ (an injective map from the projector's
six stacks to stacks of $M$, with a bijection between the corresponding alphabets) and a label map $\varphi$: at
every label $\ell$ where the projector does not halt, the statement of $M$ at $\varphi(\ell)$ is the projector's
statement at $\ell$ transported along $E$ and $\varphi$.

Let $x$ be a bit string, $v$ a Boolean and $S$ stack contents of $M$ whose embedded stacks hold splitter input $x$
and are otherwise empty. Then there are an internal state $v'$ and stack contents $T$ such that

- $M$ goes from label $\varphi(\mathrm{pair}(\mathrm{read}))$, internal state $v$ and stacks $S$ to label
  $\varphi(\text{good})$ if the [decoder of pairs of natural numbers](decode-pair-nat.md) succeeds on $x$ and
  $\varphi(\text{bad})$ if it fails, with internal state $v'$ and stacks $T$, in at most $2|x| + 6$ steps;
- $T$ and $S$ agree on every stack of $M$ outside the image of $E$;
- if the decoder returns $(m, n)$ on $x$, then the embedded stacks of $T$ hold the binary code of $m$ on the left
  output, the binary code of $n$ on the right output, and are otherwise empty.
