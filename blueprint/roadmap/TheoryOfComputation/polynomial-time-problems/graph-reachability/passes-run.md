# The pass loop of the marking machine

Let $n, k \in \mathbb{N}$, let $es$ be a list of
pairs of natural numbers with edge bits $b$, and let $m$ be a list of $n$ marks. Start the marking
machine at the label `pass`, with any flag, from stacks on which $N$ holds $k$ counter units, $X$,
$P$, $U$ and $V$ are empty, $E$ holds the reverse of $b$ and $M$ holds $m$, both as bit symbols.
Then within $k(5|b| + 3) + 1$ steps the machine reaches the label `goT`, with $M$ holding
$p^k(m)$ as bit symbols, where $p$ is one marking pass over $es$ on $n$ vertices, with $P$ empty,
and with every stack other than $N$, $X$, $E$, $M$, $U$, $V$ and $P$ unchanged.
