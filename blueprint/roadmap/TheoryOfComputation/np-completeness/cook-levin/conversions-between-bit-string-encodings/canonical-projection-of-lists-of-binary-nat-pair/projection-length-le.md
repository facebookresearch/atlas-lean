# Projected pair lists total at most four times the input length

A list of pairs of natural numbers is coded as the concatenation of the framed forms of the codes of its pairs (a
pair $(m, n)$ is coded by the framed binary code of $m$ followed by the binary code of $n$); a list of natural
numbers is coded as the concatenation of the framed binary codes of its entries.

For every bit string $x$, if the decoder of lists of pairs of natural numbers returns
$((m_1, n_1), \ldots, (m_k, n_k))$ on $x$, then the codes of the lists $(m_1, \ldots, m_k)$ and
$(n_1, \ldots, n_k)$ have total length at most $4|x|$. The blocks of $x$ need not be canonical codes.
