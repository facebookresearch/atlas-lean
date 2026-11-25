# Run of the mark-return loop of the subset-sum emitter

Let $n, w \in \mathbb{N}$ with
$w + 1 < n$. Start the VERTEX-COVER to SUBSET-SUM machine at label $\mathsf{rs}$ with any state
bit and with stacks $S$ in which stack $\mathsf{L}$ is empty and stack $\mathsf{R}$ holds, top
first, the symbols $\mathrm{val}(b_0), \dots, \mathrm{val}(b_{n-1})$, where $b_i$ is true exactly
when $i = w + 1$. Then after exactly $n + 1$ steps the machine is at label $\mathsf{vtx}$ with
some state bit and stacks $S'$ in which $\mathsf{R}$ is empty, $\mathsf{L}$ holds, top first, the
symbols $\mathrm{val}(c_{n-1}), \dots, \mathrm{val}(c_0)$, where $c_i$ is true exactly when
$i = w$, and every stack other than $\mathsf{R}$ and $\mathsf{L}$ is as in $S$. So the vertex
mark moves from vertex $w + 1$ to vertex $w$.
