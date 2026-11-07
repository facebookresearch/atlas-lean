# Self-delimiting form of a bitstring

The self-delimiting form of a bitstring
$(b_1, \dots, b_n)$ is $(\mathrm{true}, b_1, \dots, \mathrm{true}, b_n, \mathrm{false})$: each
bit is preceded by $\mathrm{true}$ and the block is terminated by $\mathrm{false}$. In
particular the empty bitstring becomes $(\mathrm{false})$.
