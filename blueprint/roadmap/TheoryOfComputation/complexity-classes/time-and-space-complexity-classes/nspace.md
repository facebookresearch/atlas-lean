# Nondeterministic space classes

For $s : \mathbb{N} \to \mathbb{N}$, $\mathrm{NSPACE}(s)$
is the set of languages $L$ of bitstrings for which there are natural numbers $c_1$, $c_2$, $k$
and a nondeterministic multi-tape Turing machine $M$ over the boolean alphabet with finitely many
states and $k$ work tapes that decides $L$ in space $c_1 s(n) + c_2$: on every input $x$, every
computation path of $M$ visits at most $c_1 s(|x|) + c_2$ work-tape cells in total, where $|x|$
is the length of $x$, and $x \in L$ if and only if some computation path of $M$ on $x$ ends in a
halted configuration whose output is the one-element list $[\mathrm{true}]$.
