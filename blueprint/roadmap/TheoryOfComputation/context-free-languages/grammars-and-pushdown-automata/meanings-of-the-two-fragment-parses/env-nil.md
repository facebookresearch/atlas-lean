# The empty environment

The fragment is a small context-free grammar for sentences such as "everybody admires someone", whose parse trees are compiled into terms of a simply typed lambda calculus over two base types, entities $e$ and truth values $t$. A model consists of a set $D$ of entities, a predicate "person" on $D$ and a binary relation "admire" on $D$. An environment for a typing context assigns to each variable of the context a value of its type. For the empty context there are no variables, and the environment for it is the unique, empty assignment.
