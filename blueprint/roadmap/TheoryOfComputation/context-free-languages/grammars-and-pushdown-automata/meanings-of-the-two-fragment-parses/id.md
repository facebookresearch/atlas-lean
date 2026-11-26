# Interpretation of the base types of the fragment

The fragment is a small context-free grammar for sentences such as "everybody admires someone", whose parse trees are compiled into terms of a simply typed lambda calculus over two base types, entities $e$ and truth values $t$. A model consists of a set $D$ of entities, a predicate "person" on $D$ and a binary relation "admire" on $D$. For a set $D$, the base types are interpreted by sending the entity type $e$ to $D$ and the truth-value type $t$ to the type of propositions.
