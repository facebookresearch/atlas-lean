# Predicates recognizable by a single-tape nondeterministic machine

Let $\alpha$ be a type
with a primitive recursive encoding into $\mathbb{N}$. A predicate $p$ on $\alpha$ is recognizable
by a single-tape nondeterministic machine when there are a finite set of states, a finite tape
alphabet $\Sigma$ with decidable equality, an injective map $\iota$ from the bits $\{0, 1\}$ to
$\Sigma$ and a single-tape nondeterministic Turing machine $M$ with these states over $\Sigma$
such that for every $a \in \alpha$, $M$ accepts the input word obtained by writing the binary
encoding of the code of $a$ in $\mathbb{N}$ letter by letter through $\iota$ if and only if
$p(a)$ holds. Here $M$ accepts a word when some run of $M$ from one of its start states on the
tape holding the word, with the head on its first symbol, reaches an accepting state.

In this model a machine cannot test whether a cell is blank, so a machine that accepts a word
accepts every extension of the word on the right. Every such predicate is recognizable by a
single-tape deterministic machine, but not conversely: the predicate $n = 0$ on $\mathbb{N}$ is
decidable by a single-tape deterministic machine and is not recognizable by a single-tape
nondeterministic machine.

## Sources

- the pinned CSLib definition of nondeterministic machines; the upstream PR leanprover/cslib#1039 lets machines read and write blank cells.
