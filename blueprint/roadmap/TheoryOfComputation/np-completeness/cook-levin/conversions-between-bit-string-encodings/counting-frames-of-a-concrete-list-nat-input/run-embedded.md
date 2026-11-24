# Embedded frame counter preserves caller stacks

Let $M$ be a multi-stack Turing machine with Boolean internal state, stacks $J$ and labels $L$, and suppose it
contains the [frame counter](prog.md) through a stack embedding $E$ (an injective map from the counter's three
stacks to stacks of $M$, with a bijection between the corresponding alphabets) and a label map $\varphi$: at every
label $\ell$ where the frame counter does not halt, the statement of $M$ at $\varphi(\ell)$ is the counter's
statement at $\ell$ transported along $E$ and $\varphi$.

Let $x$ be a bit string, $v$ a Boolean and $S$ stack contents of $M$ whose embedded stacks hold input $x$, an empty
scratch stack and an empty counter. Then there are an internal state $v'$ and stack contents $T$ such that

- $M$ goes from label $\varphi(\text{loop})$, internal state $v$ and stacks $S$ to label $\varphi(\text{good})$ if
  the [decoder of lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md)
  succeeds on $x$ and $\varphi(\text{bad})$ if it fails, with internal state $v'$ and stacks $T$, in at most
  $4|x| + 2$ steps;
- $T$ and $S$ agree on every stack of $M$ outside the image of $E$;
- if the decoder returns a list of length $k$ on $x$, then the embedded stacks of $T$ hold an empty input, an empty
  scratch stack and the counter $1^k$.
