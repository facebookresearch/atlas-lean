# Embedded list canonicalizer preserves outside stacks

Let $M$ be a multi-stack Turing machine with Boolean internal state, stacks $J$ and labels $L$, and suppose it
contains the [list canonicalizer](prog.md) through a stack embedding $E$ (an injective map from the
canonicalizer's six stacks to stacks of $M$, with a bijection between the corresponding alphabets) and a label map
$\varphi$: at every label $\ell$ where the canonicalizer does not halt, the statement of $M$ at $\varphi(\ell)$ is
the canonicalizer's statement at $\ell$ transported along $E$ and $\varphi$.

Let $x$ be a bit string, $v$ a Boolean and $S$ stack contents of $M$ whose embedded stacks hold input $x$ and are
otherwise empty. Then there are an internal state $v'$ and stack contents $T$ such that

- $M$ goes from label $\varphi(\text{loop})$, internal state $v$ and stacks $S$ to label $\varphi(\text{good})$ if
  the [decoder of lists of natural numbers](../canonicalization-of-the-concrete-binary-list-nat/decode-list-nat.md)
  succeeds on $x$ and $\varphi(\text{bad})$ if it fails, with internal state $v'$ and stacks $T$, in at most
  $11|x| + 2$ steps;
- $T$ and $S$ agree on every stack of $M$ outside the image of $E$;
- if the decoder returns a list $a$ on $x$, then the embedded stacks of $T$ are empty except the output, which holds
  the canonical code of $a$.
