# Embedded four-output decoder preserves outside stacks

Let $M$ be a multi-stack Turing machine with Boolean internal state, stacks $J$ and labels $L$, and suppose it
contains the [four-output decoder](prog.md) through a stack embedding $E$ (an injective map from the decoder's
seventeen stacks to stacks of $M$, with a bijection between the corresponding alphabets) and a label map $\varphi$:
at every label $\ell$ where the decoder does not halt, the statement of $M$ at $\varphi(\ell)$ is the decoder's
statement at $\ell$ transported along $E$ and $\varphi$.

Let $x$, $o_w$, $o_v$, $o_c$, $o_t$ be bit strings, $v$ a Boolean and $S$ stack contents of $M$ whose embedded
stacks hold $\mathrm{st}(\varepsilon, x, o_w, o_v, o_c, o_t)$. Then there are an internal state $w$ and stack
contents $T$ such that

- $M$ goes from label $\varphi(\mathrm{split}(\mathrm{read}))$, internal state $v$ and stacks $S$ to label
  $\varphi(\text{good})$ if the decoder of [run on success](run-some.md) succeeds on $x$ and $\varphi(\text{bad})$
  if it fails, with internal state $w$ and stacks $T$, in at most $9|x| + 2$ steps;
- $T$ and $S$ agree on every stack of $M$ outside the image of $E$;
- if the decoder returns $(((m_1, n_1), \ldots, (m_k, n_k)), (c, t))$ on $x$, then the embedded stacks of $T$ hold
  the final stack contents described in [run on success](run-some.md).
