# Run of the target-bit loop of the subset-sum emitter

Let $l = (b_1, \dots, b_m)$ be a
list of bits. Start the VERTEX-COVER to SUBSET-SUM machine at label $\mathsf{tem}$ with any state
bit and with stacks $S$ in which stack $\mathsf{T}$ holds exactly the bit symbols of
$b_1, \dots, b_m$, top first. Then after exactly $m + 1$ steps the machine is at label
$\mathsf{done}$ with some state bit and stacks $S'$ in which the output stack $\mathsf{O}$ holds,
top first, $\mathrm{true}, b_m, \mathrm{true}, b_{m-1}, \dots, \mathrm{true}, b_1$ followed by the
contents of $\mathsf{O}$ in $S$, and every stack other than $\mathsf{T}$ and $\mathsf{O}$ is as in
$S$. That is, each popped bit $b$ is written as $b$ and then $\mathrm{true}$.
