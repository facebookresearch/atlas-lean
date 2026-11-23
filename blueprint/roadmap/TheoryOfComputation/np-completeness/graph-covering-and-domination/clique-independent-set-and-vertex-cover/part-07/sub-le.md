# Subtraction loop of the clique reduction machine

Let $m$ be a mode of the machine, let
$k \le n$ be natural numbers, and let $S$ be stack contents in which the counter stack $A$ holds
$U^k$ ($k$ copies of the unit symbol $U$) and the counter stack $D$ holds $U^n$. Then for every
Boolean local state $v$ there are a local state $v'$ and stack contents $S'$ such that the machine
of mode $m$ runs in exactly $k + 1$ steps from label $\mathsf{sub}$ with local state $v$ and
stacks $S$ to label $\mathsf{outY}$ with local state $v'$ and stacks $S'$, the stack $D$ of $S'$
holds $U^{n-k}$, and every stack other than $A$ and $D$ has the same contents in $S'$ as in $S$.
