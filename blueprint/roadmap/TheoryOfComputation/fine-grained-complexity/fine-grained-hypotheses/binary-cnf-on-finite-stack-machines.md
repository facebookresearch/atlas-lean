# Binary CNF encodings on finite-stack Turing machines

A deterministic finite-stack Turing machine has finite control, finitely many stacks, and a finite alphabet for every stack. One step executes a labelled block, ending at a jump or a halt. The input and output stack alphabets each have a specified bijection with the two bits. A computation starts with its input on the input stack and all other stacks empty; successful termination has exactly the output stack contents specified, the other stacks empty, and the internal state reset.

On $n$ variables a literal is a pair $(i,b)$, $0\le i<n$, with $b$ the value that satisfies it. A clause is a list, a formula is a list of clauses. For width $k$ each clause has length at most $k$ and the formula's list of clauses has no repeats. Reordering a clause can change it; repetitions *inside* a clause are allowed. The empty clause is false. The word begins with $1^n0$, then each clause is written in order using $k$ slots, padded with zero slots on the right. A slot is the little-endian binary representation of $0$ for padding, $2i+1$ for a negative literal or $2i+2$ for a positive literal, in $\lfloor\log_2(2n)\rfloor+1$ bits (one bit for $n=0$). To supply $k$ as input, prepend $1^k0$.

## Expansion

Specify the input and output alphabets and the exact initialization and halt/reset conditions in the common machine interface. A translation to another SAT encoding needs an explicit size bound and a proof that this machine can execute it within the relevant time.

## Sources

- Anthropic, [binary conventions and machine semantics](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/eth/MainResults.lean#L18-L91).
