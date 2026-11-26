# The middle slice function

For $n\ge1$ let $a(n)=\lceil n/2\rceil-\lfloor\sqrt{n+1}/10\rfloor$. The *middle slice* $\mathrm{MS}_n:\{0,1\}^n\to\{0,1\}$ accepts exactly the strings with exactly $a(n)$ zeros. The language $\mathrm{MS}=\bigcup_n\mathrm{MS}_n^{-1}(1)$ is decided in polynomial time (by counting zeros).

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR, 1987.
- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), 2016.
