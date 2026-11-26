# Randomized word RAMs and expected running time

A **randomized word RAM** with word size $w$ is a word RAM with an additional instruction that writes a uniformly random $w$-bit word (or a uniformly random value below a register's content) into a register. A program induces, on each input, a probability distribution over halting outputs and running times; its **expected running time** is the expectation of the number of executed instructions (possibly infinite). Structured programs (sequencing, conditionals, while loops) have exact output laws obtained compositionally: sequencing is the monadic bind of the laws, and a while loop's law is the least fixed point of its unfolding.

## Depends on

- [The word-RAM model](../../fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Torben Hagerup, "Sorting and Searching on the Word RAM", STACS 98, 1998.
- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
