# DTIME over codes

For every $t : \mathbb{N} \to \mathbb{N}$ and every language $L$ of
binary words, $L \in \mathsf{DTIME}(t)$ if and only if there are natural numbers $c_1, c_2, k$
and a code $c$ with $k$ work tapes such that the machine of $c$ decides $L$, on every input $w$
runs in time $c_1 t(|w|) + c_2$, and for some $s : \mathbb{N} \to \mathbb{N}$ on every input
$w$ runs in space $s(|w|)$.
