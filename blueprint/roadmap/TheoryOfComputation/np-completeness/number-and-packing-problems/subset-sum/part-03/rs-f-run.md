# Subset-sum emitter: moving unmarked vertices back to L

Let $c$ be a natural number,
$\rho = (\rho_1, \dots, \rho_k)$ a list of bits, $v$ a Boolean state and $S$ stack contents whose
stack $R$ holds, top first, $c$ copies of $\mathrm{val}(\mathrm{false})$ followed by
$\mathrm{val}(\rho_1), \dots, \mathrm{val}(\rho_k)$. Then $c$ steps of the subset-sum emitter
machine lead from label $\mathrm{rs}$ with state $v$ and stacks $S$ back to label $\mathrm{rs}$
with some state and some stacks $S'$ such that $S'(R)$ is
$\mathrm{val}(\rho_1), \dots, \mathrm{val}(\rho_k)$, $S'(L)$ is $c$ copies of
$\mathrm{val}(\mathrm{false})$ followed by $S(L)$, and every stack other than $R$ and $L$ is
unchanged.
