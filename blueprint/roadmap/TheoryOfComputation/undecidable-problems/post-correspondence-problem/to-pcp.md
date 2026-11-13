# The reduction from MPCP to PCP

Write $\star$ for the star and $\diamond$ for the end
marker of the extended alphabet; for a word $u$ over $\alpha$, $\star u$ puts a star before every
letter of $u$ and $u \star$ puts a star after every letter of $u$. The empty list of dominoes is
sent to the empty list. A list $P = [d_0, d_1, \ldots, d_n]$ of dominoes over $\alpha$, with
$d_0 = (t_0, b_0)$, is sent to the following list of dominoes over the extended alphabet: first
the start domino $(\star t_0, \star b_0 \star)$, then the domino $(\star t, b \star)$ for each
domino $(t, b)$ of $P$ in order (including $d_0$), and last the end domino
$(\star \diamond, \diamond)$, whose top word is a star followed by the end marker.
