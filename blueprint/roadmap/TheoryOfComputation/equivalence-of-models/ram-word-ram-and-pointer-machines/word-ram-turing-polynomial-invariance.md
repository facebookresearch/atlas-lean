# Polynomial time on the word RAM equals polynomial time on multi-tape Turing machines

(i) A multi-tape Turing machine running in $t$ steps is simulated by a fixed word-RAM program (over the additive basis) in $O(t)$ instructions at every word size $w$ able to hold addresses linear in $t$ and the input length. (ii) A function with binary output is computable in polynomial time by a multi-tape Turing machine if and only if a single fixed word-RAM program computes it on the bits of its input within polynomially many instructions at every word size above a logarithmic threshold and below a polynomial one. Hence $\mathsf{P}$ is model-invariant between these machines.

## Proof sketch

(i) Store each tape as an array and the head positions in registers; one machine step is a constant number of RAM instructions. (ii) Conversely, a Turing machine maintains the RAM's registers and a sparse memory as lists of address–value pairs; each word-RAM instruction on $w=O(\log n)$-bit words costs polynomial time.

## Depends on

- [The word-RAM model](../../fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
- Torben Hagerup, "Sorting and Searching on the Word RAM", STACS 98, 1998.
