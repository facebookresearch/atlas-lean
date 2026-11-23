# Subset-sum emitter: one vertex number

Stacks are listed top first. Let $n$ be a natural
number, $p_0, \dots, p_{P-1}$ the pairs $(i, j)$ with $i < j < n$ in encoding order (rows $i$
ascending, within a row $j$ descending), $(\beta_0, \dots, \beta_{P-1})$ a list of $P$ pair bits
and $w < n$ a vertex. Let $N_w = 4^P + \sum_q 4^q$, the sum over the $q < P$ such that $\beta_q$
is true and $w$ is an endpoint of $p_q$, and let $m_u$ be true if $u = w$ and false otherwise.
Let $v$ be a Boolean state and $S$ stack contents such that $S(L)$ is
$\mathrm{val}(m_{n-1}), \dots, \mathrm{val}(m_0)$, $S(Y)$ is
$\mathrm{val}(\beta_{P-1}), \dots, \mathrm{val}(\beta_0)$, and $S(R)$, $S(\mathrm{Rt})$ and $S(Z)$
are empty. Then $3P + 3n + 2$ steps of the subset-sum emitter machine lead from label
$\mathrm{vtx}$ with state $v$ and stacks $S$ to label $\mathrm{vchk}$ with some state and some
stacks $S'$ such that: $S'(L)$, $S'(\mathrm{Rt})$ and $S'(Z)$ are empty; $S'(R)$ is
$\mathrm{val}(m_0), \dots, \mathrm{val}(m_{n-1})$; $S'(Y) = S(Y)$; $S'(O)$ is the self-delimiting
encoding of the binary representation of $N_w$ (least significant bit first) followed by $S(O)$;
and every stack other than $L$, $R$, $\mathrm{Rt}$, $Y$, $Z$ and $O$ is unchanged.
