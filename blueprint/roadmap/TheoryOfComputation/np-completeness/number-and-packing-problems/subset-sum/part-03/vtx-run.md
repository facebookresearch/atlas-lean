# Run of the vertex-number phase of the subset-sum emitter

Let $n \in \mathbb{N}$, let
$p_0, \dots, p_{P-1}$ be the vertex pairs $(i, j)$ with $i < j < n$, listed with $i$ ascending
and, for each $i$, with $j$ descending, let $\beta_0, \dots, \beta_{P-1}$ be bits, and let
$w < n$. For a vertex $u$ let $a_u$ be $4^P$ plus the sum of $4^q$ over the indices $q < P$ such
that $\beta_q$ is true and $p_q$ contains $u$. Start the VERTEX-COVER to SUBSET-SUM machine at
label $\mathsf{vtx}$ with any state bit and with stacks $S$ in which stack $\mathsf{L}$ holds, top
first, the symbols $\mathrm{val}(c_{n-1}), \dots, \mathrm{val}(c_0)$, where $c_i$ is true exactly
when $i = w$, the stacks $\mathsf{R}$, $\mathsf{Rt}$ and $\mathsf{Z}$ are empty, and stack
$\mathsf{Y}$ holds, top first, the symbols
$\mathrm{val}(\beta_{P-1}), \dots, \mathrm{val}(\beta_0)$. Then within at most
$(w + 1)(3P + 4n + 4)$ steps the machine reaches label $\mathsf{hv}$ with some state bit and
stacks $S'$ in which the output stack $\mathsf{O}$ holds, top first, the self-delimiting binary
encodings of $a_0, a_1, \dots, a_w$ followed by the contents of $\mathsf{O}$ in $S$, and every
stack other than $\mathsf{L}$, $\mathsf{R}$, $\mathsf{Rt}$, $\mathsf{Y}$, $\mathsf{Z}$ and
$\mathsf{O}$ is as in $S$. Here the binary encoding lists the bits least significant first, and
the self-delimiting encoding replaces each bit $b$ by $\mathrm{true}, b$ and appends
$\mathrm{false}$.
