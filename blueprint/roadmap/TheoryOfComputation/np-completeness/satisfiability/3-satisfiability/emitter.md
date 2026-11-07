# Emitter

An emitter is a multi-stack machine, given by a type of stacks and a type of
labels (both with decidable equality), an alphabet for each stack and a program with boolean
state, together with a start label and a different exit label at which the program halts, a
token stack and a different output stack, a bijection from the SAT token symbols to the token
stack's alphabet, a bijection from the output stack's alphabet to the booleans, an output map
$g$ from CNF formulas to bit strings, a bit string reserved as the output for undecodable inputs,
and a monotone step bound $B : \mathbb{N} \to \mathbb{N}$. It must satisfy: for every CNF formula
$\varphi$ whose token sequence has length $n$, every initial state, and all stack contents in
which the token stack holds the token sequence of $\varphi$ in reverse, each token translated by
the token bijection, and every other stack is empty, the program goes from the start label to
the exit label in at most $B(n)$ steps and ends with the output stack holding $g(\varphi)$, each
bit translated by the inverse of the output bijection.
