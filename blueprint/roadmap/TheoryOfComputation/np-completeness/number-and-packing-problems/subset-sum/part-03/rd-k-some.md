# Subset-sum emitter: reading the unary k

Let $k$ and $i$ be natural numbers, $v$ a Boolean
state, $r = (r_1, \dots, r_m)$ a list of bits and $S$ stack contents such that stack $X$ holds,
top first, $k$ copies of $\mathrm{bit}(\mathrm{true})$, then $\mathrm{bit}(\mathrm{false})$, then
$\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, and stack $A$ holds exactly $i$ copies of the
counter unit $U$. Then $k + 1$ steps of the subset-sum emitter machine lead from label
$\mathrm{rdK}$ with state $v$ and stacks $S$ to label $\mathrm{rdN}$ with some state and some
stacks $S'$ such that $S'(X)$ is $\mathrm{bit}(r_1), \dots, \mathrm{bit}(r_m)$, $S'(A)$ holds
exactly $i + k$ copies of $U$, and every stack other than $X$ and $A$ is unchanged.
