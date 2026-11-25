# DSPACE over codes

For every $s : \mathbb{N} \to \mathbb{N}$ and every language $L$ of
binary words, $L \in \mathsf{DSPACE}(s)$ if and only if there are natural numbers $c_1, c_2, k$
and a code $c$ with $k$ work tapes such that the machine of $c$ decides $L$, on every input $w$
runs in space $c_1 s(|w|) + c_2$, and for some $t : \mathbb{N} \to \mathbb{N}$ on every input
$w$ runs in time $t(|w|)$.
