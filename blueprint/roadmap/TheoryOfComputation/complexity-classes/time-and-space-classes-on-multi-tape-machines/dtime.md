# Deterministic time classes on multi-tape machines

For $t : \mathbb{N} \to \mathbb{N}$,
$\mathrm{DTIME}(t)$ is the set of languages $L$ of Boolean strings for which there are constants
$c_1, c_2 \in \mathbb{N}$, a function $s : \mathbb{N} \to \mathbb{N}$ and a deterministic
multi-tape Turing machine with Boolean tape alphabet and finitely many states such that, on every
input $w$ of length $n$, the machine halts with the one-bit output $[\mathrm{true}]$ if $w \in L$
and $[\mathrm{false}]$ otherwise, runs in time $c_1 t(n) + c_2$ (every computation path of at
least $c_1 t(n) + c_2$ steps ends in a halted configuration) and runs in space $s(n)$ (every
computation path visits at most $s(n)$ work-tape cells, summed over the work tapes).
