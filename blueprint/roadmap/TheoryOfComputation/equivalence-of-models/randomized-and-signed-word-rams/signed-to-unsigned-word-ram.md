# Signed RAM programs compile to the unsigned word RAM with constant overhead

Represent signed integers in $w$-bit words by an offset (or sign–magnitude) encoding. Every program of a RAM operating on signed integers with addition, subtraction, comparison and the usual tests can be compiled into an unsigned word-RAM program that, at every word size $w$ large enough to hold twice the largest absolute value reached plus one bit, simulates each signed instruction by $O(1)$ unsigned instructions and produces the encoded signed output; input preparation (encoding the signed input) is charged linearly.

## Proof sketch

Signed addition and comparison reduce to unsigned operations on encodings with a constant number of corrections for carries and signs; a state-representation invariant relates signed registers to their encodings and is preserved by each compiled instruction.

## Depends on

- [The word-RAM model](../../fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Torben Hagerup, "Sorting and Searching on the Word RAM", STACS 98, 1998.
- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
