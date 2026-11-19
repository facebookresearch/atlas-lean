# Four-output decoder emits four canonical outputs on success

An element $(((m_1, n_1), \ldots, (m_k, n_k)), (c, t))$ is coded as the framed form of the code of the list of
pairs (see [projection length](../canonical-projection-of-lists-of-binary-nat-pair/projection-length-le.md))
followed by the code of the pair $(c, t)$. Let $x$ be a bit string on which the decoder of such elements returns
$(((m_1, n_1), \ldots, (m_k, n_k)), (c, t))$, let $o_w$, $o_v$, $o_c$, $o_t$ be bit strings and $v$ a Boolean.
There is an internal state $w$ such that the [four-output decoder](prog.md) goes from label
$\mathrm{split}(\mathrm{read})$, internal state $v$ and stacks $\mathrm{st}(\varepsilon, x, o_w, o_v, o_c, o_t)$ (see
the [stack invariant](st.md)) to label good, internal state $w$ and stacks
$\mathrm{st}(\varepsilon, \varepsilon, o_w', o_v', o_c', o_t')$ in at most $9|x| + 2$ steps, where $o_w'$ is the
code of $(m_1, \ldots, m_k)$ followed by $o_w$, $o_v'$ the code of $(n_1, \ldots, n_k)$ followed by $o_v$, $o_c'$
the binary code of $c$ followed by $o_c$, and $o_t'$ the binary code of $t$ followed by $o_t$.
