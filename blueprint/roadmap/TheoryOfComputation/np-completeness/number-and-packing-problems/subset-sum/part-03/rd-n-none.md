# Subset-sum emitter: unterminated unary prefix at rdN

Let $r = (r_1, \dots, r_m)$ be a
list of bits on which reading a unary length prefix fails (equivalently, no $r_i$ is
$\mathrm{false}$). Then for every Boolean state $v$ and all stack contents $S$ whose stack $X$
holds $\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, top first, $m + 1$ steps of the subset-sum
emitter machine lead from label $\mathrm{rdN}$ with state $v$ and stacks $S$ to label
$\mathrm{bad}$ with some state and some stacks that agree with $S$ on every stack other than $X$,
$N$ and $L$.
