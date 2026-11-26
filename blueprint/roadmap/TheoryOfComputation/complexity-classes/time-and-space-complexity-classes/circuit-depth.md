# Depth of a flat Boolean circuit

The depth of a circuit, given as a list of gates, is
the maximum of the depths of its gates, and $0$ for the empty circuit. Input and constant gates
have depth $0$; a negation, and, or or mod gate has depth one more than the maximum depth of the
gates it references (the maximum over no references is $0$), where a reference to a gate that
does not come earlier in the list counts as depth $0$.
