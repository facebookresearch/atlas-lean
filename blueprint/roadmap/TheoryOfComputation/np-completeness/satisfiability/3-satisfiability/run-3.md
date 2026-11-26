# Tokenize, then emit

Let $E$ be an emitter with step bound $B$, and let $x$ be a bit
string. The tokenize-then-emit machine for $E$, started at its start label with internal state
false, with $x$ as bit symbols on the tokenizer's input stack and every other stack empty,
reaches its exit label, with some internal state, in at most $2|x| + 3 + B(|x|)$ steps, and the
output stack of $E$ then holds the output on $x$, written in the output symbols of $E$.
