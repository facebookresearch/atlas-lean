# Polynomial time bound for the clause-family generator

Let $L$ be a layout,
$\mathit{la}, \mathit{na} : \mathbb{N} \to \mathbb{N}$ and
$\mathit{wa} : \mathbb{N}^3 \to \mathbb{N}$ tables, and $N, T, H \in \mathbb{N}$, and suppose the
tables are well formed at height $H$ for every situation $i < N$. Start the generator for $L$,
$\mathit{la}$, $\mathit{na}$, $\mathit{wa}$ and $N$ at its first precomputation stage, in state
false, with $T$ on the time counter and $H$ on the height counter in unary, all other counters
empty, and an arbitrary list $o$ of bits on the output stack. Then within $c\,(T + H + 1)^5$
steps, where $c$ is the constant of the generator's time bound for $L$ and $N$, it reaches its
final label $\mathsf{done}$ (not the error stage of the literal routine, which also halts), in some
state, with stacks whose output stack holds the encoding of the clause family for $L$,
$\mathit{la}$, $\mathit{na}$, $\mathit{wa}$, $T$, $H$ and $N$, followed by $o$.
