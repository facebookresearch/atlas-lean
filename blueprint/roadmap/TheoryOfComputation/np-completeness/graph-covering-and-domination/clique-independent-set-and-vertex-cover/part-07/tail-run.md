# Number output of the clique reduction machine

Let $m$ be a mode of the machine and $C$
its final counter stack ($A$ for the flip mode, $D$ for the vertex-cover mode). Let $n, c$ be
natural numbers, $u$ a symbol of the alphabet of $C$, and $S$ stack contents in which the stack
$B$ holds $U^n$ ($n$ copies of the unit symbol $U$) and $C$ holds $u^c$. Then for every Boolean
local state $v$ there are a local state $v'$ and stack contents $S'$ such that the machine of
mode $m$ runs in exactly $n + c + 3$ steps from label $\mathsf{outB}$ with local state $v$ and
stacks $S$ to label $\mathsf{done}$ with local state $v'$ and stacks $S'$, and the output stack
$O$ of $S'$ holds, from the top, $c$ copies of $\mathrm{true}$, then $\mathrm{false}$, then $n$
copies of $\mathrm{true}$, then the contents of $O$ in $S$.
