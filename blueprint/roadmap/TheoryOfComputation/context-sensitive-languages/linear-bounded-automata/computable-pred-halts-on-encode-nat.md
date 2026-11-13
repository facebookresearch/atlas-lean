# Halting of a linear bounded automaton on binary codes is decidable

Let $M$ be a
single-tape machine over a finite alphabet $\Sigma$ that is a linear bounded automaton, let
$\alpha$ be a primitive recursively coded type, and let $\iota : \{0, 1\} \to \Sigma$ be any map.
For $a \in \alpha$, let $w_a$ be the word over $\Sigma$ obtained by applying $\iota$ to each bit of
the binary expansion, least significant bit first and without leading zeros, of the
natural-number code of $a$; so $w_a$ is empty when that code is $0$. Then the set of
$a \in \alpha$ such that $M$ halts on $w_a$ is computable.
