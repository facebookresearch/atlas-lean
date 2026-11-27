# Compiling a derivation tree to its meaning

Every valid derivation tree of the seven-rule fragment is compiled, by structural recursion on the tree, to a simply typed term in the lexical context whose type is the semantic type of the tree's root category, using exactly the seven semantic actions of the fragment: the three lexical leaves ("everybody" as a subject, "someone" as an object, "admires" as a transitive verb) and the four combination rules. An invalid tree has no validity proof, so no term is assigned to it, and the result does not depend on which validity proof is used.
