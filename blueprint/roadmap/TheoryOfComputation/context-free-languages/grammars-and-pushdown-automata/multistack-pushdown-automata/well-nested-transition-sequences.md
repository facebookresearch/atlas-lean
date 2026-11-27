# Well-nested sequences and matching of push/pop transitions

In a sequence of MPDA transitions, a push on stack $s$ at position $i$ **matches** a pop on stack $s$ at position $j>i$ if, considering stack $s$ only, the factor strictly between them is balanced. A push is **pending** at a prefix if it is not matched within the prefix. The sequence is **well-nested** if every push and every pop is matched, each matched push and pop carry the same stack symbol, and the matching pairs, over all stacks together, form a properly nested (non-crossing) family; equivalently it is generated from the empty sequence and nop transitions by concatenation and by enclosing a well-nested sequence between a push and the matching pop of the same stack symbol.

## Depends on

- [Multistack pushdown automata](multistack-pushdown-automata.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020.
