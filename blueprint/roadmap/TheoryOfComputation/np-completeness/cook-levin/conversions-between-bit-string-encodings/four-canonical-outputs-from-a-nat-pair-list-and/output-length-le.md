# Four-output decoder output is at most twice the input length

For every bit string $x$, if the decoder of [run on success](run-some.md) returns
$(((m_1, n_1), \ldots, (m_k, n_k)), (c, t))$ on $x$, then the codes of $(m_1, \ldots, m_k)$ and of
$(n_1, \ldots, n_k)$ and the binary codes of $c$ and of $t$ have total length at most $2|x|$, whatever the sizes of
the decoded numbers.
