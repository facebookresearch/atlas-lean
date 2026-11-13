# Accepting run of the SAT tokenizer

Let $x$ and $w$ be bit strings such that $x$ decodes
to the CNF formula $\varphi$, and let $S$ be contents of the tokenizer's stacks in which $X$
holds the bits of $x$, $W$ holds the bits of $w$, and the counters $CC$ and $LC$ are empty.
Started at the start label with stacks $S$ and any value of its Boolean variable, the tokenizer
reaches the accepting label within $2|x| + 2$ steps, with final stacks $S'$ such that $X$, $CC$
and $LC$ are empty, $W$ holds the bits of $w$ without their first $m$ entries, where $m$ is the
number of literal occurrences in $\varphi$, $T$ holds the reversed token list of $\varphi$ on top
of the original contents of $T$, and $B$ holds the table stack of the occurrence table of
$\varphi$ and $w$ on top of the original contents of $B$.
