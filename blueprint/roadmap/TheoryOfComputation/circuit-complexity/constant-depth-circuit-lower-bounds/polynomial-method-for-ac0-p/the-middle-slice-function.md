# The middle slice function

For $n\ge1$ let $a(n)=\lceil n/2\rceil-\lfloor\sqrt{n+1}/10\rfloor$. The *middle slice* $\mathrm{MS}_n:\{0,1\}^n\to\{0,1\}$ accepts exactly the strings with exactly $a(n)$ zeros. The offset $\lfloor\sqrt{n+1}/10\rfloor$ makes $n-2a(n)$ grow like $\sqrt n/5$ while $\binom{n}{a(n)}\ge\tfrac45\,2^n/(n+1)$ for all $n\ge1$; any slice with these two properties serves Razborov's rank argument equally well. The language $\mathrm{MS}=\bigcup_n\mathrm{MS}_n^{-1}(1)$ is decided in polynomial time (by counting zeros).

## Depends on

- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR 41(4), 1987.
- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
