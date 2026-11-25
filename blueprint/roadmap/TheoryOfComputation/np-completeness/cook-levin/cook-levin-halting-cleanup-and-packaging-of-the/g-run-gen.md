# Running a program, then the drain

Let $g, r \in \mathbb{N}$, let $P$ be a program with
labels $\Lambda$ and Boolean state over the stacks of the full machine with alphabets
$F\Gamma_{g,r}$, and let $\mathit{fin}$ be a label with $P(\mathit{fin}) = \mathrm{halt}$.
Suppose $P$ goes in at most $B$ steps from the configuration with label $\ell$, state $v$ and
stacks $S$ to the configuration with label $\mathit{fin}$, state $v'$ and stacks $T$. Then the
composed program of $P$ and $\mathit{fin}$ goes in at most $B + 1 + d(T)$ steps from label $\ell$
(as a label of the composed program), state $v$ and stacks $S$ to the halted configuration with
state false in which every stack other than the output stack is empty and the output stack is
that of $T$. Here $d(T)$, the step count of the drain, is $1$ plus the sum of $|T_q| + 1$ over
the stacks $q$ other than the output stack.
