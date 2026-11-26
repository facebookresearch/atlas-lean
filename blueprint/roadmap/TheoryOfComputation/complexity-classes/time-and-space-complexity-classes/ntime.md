# Nondeterministic time classes

For $t : \mathbb{N} \to \mathbb{N}$, $\mathrm{NTIME}(t)$ is
the set of languages $L$ of bitstrings for which there are natural numbers $c_1$, $c_2$, $k$ and a
nondeterministic multi-tape Turing machine $M$ over the boolean alphabet with finitely many states
and $k$ work tapes that decides $L$ in time $c_1 t(n) + c_2$: on every input $x$, every
computation path of $M$ with at least $c_1 t(|x|) + c_2$ steps ends in a halted configuration,
where $|x|$ is the length of $x$, and $x \in L$ if and only if some computation path of $M$ on
$x$ ends in a halted configuration whose output is the one-element list $[\mathrm{true}]$.
