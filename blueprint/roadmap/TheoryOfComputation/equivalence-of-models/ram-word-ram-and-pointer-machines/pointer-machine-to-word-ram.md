# Pointer machines are simulated by word RAMs with constant overhead

Every pointer-machine program over natural-number data with standard word-RAM operations can be compiled into a word-RAM program that, on inputs whose computation allocates at most $m$ records with data values below $2^{w}$, simulates each pointer-machine instruction by $O(1)$ word-RAM instructions at every word size $w\ge\log_2(m\cdot f)+O(1)$, where $f$ is the number of fields; records are laid out as consecutive memory blocks and pointers become addresses. Pointer-machine semantics is preserved under injective heap embeddings.

## Proof sketch

Allocate records with a bump pointer; a field access is an indexed load or store at base address plus field offset. Correctness is proved by a simulation relation between the abstract heap and its embedding into word memory, preserved by every instruction.

## Depends on

- [Pointer machine](../../../ComputerScience/data-structures/search-trees/pointer-machine-search-trees/pointer-machine.md)
- [The word-RAM model](../../fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Robert Endre Tarjan, "A Class of Algorithms Which Require Nonlinear Time to Maintain Disjoint Sets", Journal of Computer and System Sciences 18(2), 1979.
- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
