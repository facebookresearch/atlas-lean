# Subset-sum emitter: reading the unary n

Let $n$ and $i$ be natural numbers, $v$ a Boolean
state, $r = (r_1, \dots, r_m)$ a list of bits and $S$ stack contents such that stack $X$ holds,
top first, $n$ copies of $\mathrm{bit}(\mathrm{true})$, then $\mathrm{bit}(\mathrm{false})$, then
$\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, stack $N$ holds exactly $i$ copies of the counter
unit $U$, and stack $L$ holds exactly $i$ copies of $\mathrm{val}(\mathrm{false})$. Then $n + 1$
steps of the subset-sum emitter machine lead from label $\mathrm{rdN}$ with state $v$ and stacks
$S$ to label $\mathrm{mv}$ with some state and some stacks $S'$ such that $S'(X)$ is
$\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, $S'(N)$ holds exactly $i + n$ copies of $U$,
$S'(L)$ holds exactly $i + n$ copies of $\mathrm{val}(\mathrm{false})$, and every stack other than
$X$, $N$ and $L$ is unchanged.
