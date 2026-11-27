# One-sided sensitivity, block sensitivity and certificate complexity

For $f : \{0,1\}^n \to \{0,1\}$, with $s(f, x)$, $bs(f, x)$ and $C(f, x)$ as on the linked page, the *$0$-sensitivity* and *$1$-sensitivity* are $s_0(f) = \max\{s(f, x) : f(x) = 0\}$ and $s_1(f) = \max\{s(f, x) : f(x) = 1\}$; analogously the *$0$-block sensitivity* and *$1$-block sensitivity* are $bs_0(f) = \max\{bs(f, x) : f(x) = 0\}$ and $bs_1(f) = \max\{bs(f, x) : f(x) = 1\}$, and the *$0$-certificate* and *$1$-certificate complexities* are $C_0(f) = \max\{C(f, x) : f(x) = 0\}$ and $C_1(f) = \max\{C(f, x) : f(x) = 1\}$.

## Proof sketch

Derived here (not stated in the cited source): take each maximum to be $0$ when $f$ never takes the value $b$, as the linked page does for $C_b$. Then directly from the definitions $s(f) = \max(s_0(f), s_1(f))$, $bs(f) = \max(bs_0(f), bs_1(f))$ and $C(f) = \max(C_0(f), C_1(f))$, and replacing $f$ by $1 - f$ swaps the indices $0$ and $1$ while leaving each two-sided measure unchanged, since $s(f, x)$, $bs(f, x)$ and $C(f, x)$ depend only on which inputs share the value $f(x)$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- A. Ambainis, M. Bavarian, Y. Gao, J. Mao, X. Sun and S. Zuo, "Tighter Relations Between Sensitivity and Other Complexity Measures", Automata, Languages, and Programming (ICALP 2014), Lecture Notes in Computer Science 8572, 2014; full version arXiv:1411.3419, Definitions 2.1, 2.2 and 2.3.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
- N. Nisan, "CREW PRAMs and Decision Trees", SIAM Journal on Computing 20(6), 1991.
