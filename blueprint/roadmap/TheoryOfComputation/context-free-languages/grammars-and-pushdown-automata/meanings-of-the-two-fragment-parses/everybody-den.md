# Meaning of the quantifier everybody

The fragment is a small context-free grammar for sentences such as "everybody admires someone", whose parse trees are compiled into terms of a simply typed lambda calculus over two base types, entities $e$ and truth values $t$. A model consists of a set $D$ of entities, a predicate "person" on $D$ and a binary relation "admire" on $D$. In a model, the word "everybody" denotes the generalized quantifier of type $(e \to t) \to t$ sending a property $P$ of entities to the proposition that $P(x)$ holds for every entity $x$ that is a person.
