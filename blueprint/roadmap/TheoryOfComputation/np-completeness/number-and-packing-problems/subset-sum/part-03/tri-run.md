# Run of the pair-counting loop of the subset-sum emitter

Let $n, p \in \mathbb{N}$ and
let $T_n = 0 + 1 + \dots + (n - 1)$. Start the VERTEX-COVER to SUBSET-SUM machine at label
$\mathsf{tri}$ with any state bit and with stacks $S$ in which the counter stacks $\mathsf{N}$ and
$\mathsf{M}$ hold exactly $n$ and $p$ unit symbols and the scratch stack $\mathsf{S1}$ is empty.
Then after exactly $(n + 1)^2$ steps the machine is at label $\mathsf{cmp}$ with some state bit
and stacks $S'$ in which $\mathsf{M}$ holds exactly $p + T_n$ unit symbols and every stack other
than $\mathsf{N}$ and $\mathsf{M}$ is as in $S$.
