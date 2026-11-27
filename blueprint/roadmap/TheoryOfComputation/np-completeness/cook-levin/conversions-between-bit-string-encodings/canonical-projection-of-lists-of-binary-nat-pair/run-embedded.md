# Embedded pair-list projector preserves outside stacks

Let $M$ be a multi-stack Turing machine with Boolean internal state, stacks $J$ and labels $L$, and suppose it
contains the [pair-list projector](prog.md) through a stack embedding $E$ (an injective map from the projector's
eleven stacks to stacks of $M$, with a bijection between the corresponding alphabets) and a label map $\varphi$: at
every label $\ell$ where the projector does not halt, the statement of $M$ at $\varphi(\ell)$ is the projector's
statement at $\ell$ transported along $E$ and $\varphi$.

Let $x$ be a bit string, $v$ a Boolean and $S$ stack contents of $M$ whose embedded stacks hold input $x$ and are
otherwise empty. Then there are an internal state $w$ and stack contents $T$ such that

- $M$ goes from label $\varphi(\text{loop})$, internal state $v$ and stacks $S$ to label $\varphi(\text{good})$ if
  the decoder of lists of pairs of natural numbers succeeds on $x$ and $\varphi(\text{bad})$ if it fails, with
  internal state $w$ and stacks $T$, in at most $16|x| + 3$ steps;
- $T$ and $S$ agree on every stack of $M$ outside the image of $E$;
- if the decoder returns $((m_1, n_1), \ldots, (m_k, n_k))$ on $x$, then the embedded stacks of $T$ hold the code
  of $(m_1, \ldots, m_k)$ on the first output, the code of $(n_1, \ldots, n_k)$ on the second output, and are
  otherwise empty.
