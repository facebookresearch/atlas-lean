# The mismatch language

**The mismatch language** of one side of a list $P$ of dominoes. Let $s$ be a map from dominoes
to words (in use, the top or the bottom), write $w_i = s(d_i)$ for the $i$-th domino $d_i$ of $P$
and $\mathrm{code}(i)$ for the unary code of $i$ as bits. The language, over letters and bits,
consists of the words $x\,\mathrm{code}(i_n) \cdots \mathrm{code}(i_1)$ where $x$ is a word of
letters and $i_1, \dots, i_n$ with $n \ge 1$ are indices below $|P|$ such that
$x \ne w_{i_1} \cdots w_{i_n}$.
