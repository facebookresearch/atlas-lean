# Every mismatched word is derivable from the mismatch nonterminal

Let $P$ be a list of
dominoes over a finite alphabet, $s$ a map from dominoes to words (in use, the top or the bottom),
$w_i = s(d_i)$ for the $i$-th domino $d_i$ of $P$, and $\mathrm{code}(i)$ the unary code of $i$ as
bits. Let $A$ be a nonterminal such that every mismatch production of $A$ for $s$ and $P$ is a
production of the universality grammar of $P$. Then for every nonempty sequence
$i_1, \dots, i_n$ of indices below $|P|$ and every word $x$ of letters with
$x \ne w_{i_1} \cdots w_{i_n}$, the word $x\,\mathrm{code}(i_n) \cdots \mathrm{code}(i_1)$ is
derivable from $A$ in the universality grammar of $P$.
