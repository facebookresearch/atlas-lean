# Deterministic space classes on multi-tape machines

For $s : \mathbb{N} \to \mathbb{N}$,
$\mathrm{DSPACE}(s)$ is the set of languages $L$ of Boolean strings for which there are constants
$c_1, c_2 \in \mathbb{N}$, a function $t : \mathbb{N} \to \mathbb{N}$ and a deterministic
multi-tape Turing machine with Boolean tape alphabet and finitely many states such that, on every
input $w$ of length $n$, the machine halts with the one-bit output $[\mathrm{true}]$ if $w \in L$
and $[\mathrm{false}]$ otherwise, runs in time $t(n)$ (every computation path of at least $t(n)$
steps ends in a halted configuration) and runs in space $c_1 s(n) + c_2$ (every computation path
visits at most $c_1 s(n) + c_2$ work-tape cells, summed over the work tapes).
