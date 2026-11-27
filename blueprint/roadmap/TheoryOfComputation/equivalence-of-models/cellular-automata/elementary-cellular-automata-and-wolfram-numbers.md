# Elementary cellular automata and Wolfram numbers

An *elementary* cellular automaton is a one-dimensional [cellular automaton](cellular-automata-on-z-d.md) with state set
$\{0, 1\}$ and neighborhood $(-1, 0, 1)$, so that each cell's next state is $f(c_{i-1}, c_i, c_{i+1})$. There are
$2^8 = 256$ of them. The *Wolfram number* of such an automaton is the integer in $\{0, \dots, 255\}$ whose binary expansion is
$f(111)\,f(110)\,f(101)\,f(100)\,f(011)\,f(010)\,f(001)\,f(000)$. For instance *rule 110* is the elementary cellular automaton
with $f(111) = f(100) = f(000) = 0$ and $f(110) = f(101) = f(011) = f(010) = f(001) = 1$, since $110 = (01101110)_2$.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.5.
- M. Cook, "Universality in elementary cellular automata", *Complex Systems* 15(1):1–40, 2004, Section 1 (the local rule of rule 110).
