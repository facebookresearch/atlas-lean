# Clique emitter: comparing two names

Let $p$, $q$ and $v$ be Booleans, $u$ and $w$ lists
of bits, $t$, $e$ and $R$ stack-symbol lists with $R$ empty or not starting with a name bit, $o$
a list of bits and $c, n \in \mathbb{N}$. Let $b$ be $(p = q)$ if $u = w$ and true otherwise.
For some flag $v'$, the emitter machine goes in at most $3|w| + 4$ steps from label
$\mathrm{cmp}(p, q)$ with flag $v$ and the state with token stack $t$, output $o$, name stack
$u$, walked stack $w$ followed by $R$, walk side $e$, clause count $c$, occurrence count $n$ and
empty scratch stacks to label $\mathrm{mvN}(p, \mathrm{true})$ with flag $v'$ and the same state
except that the output is $b$ followed by $o$. Here $u$ and $w$ lie on the stacks as name-bit
symbols.
