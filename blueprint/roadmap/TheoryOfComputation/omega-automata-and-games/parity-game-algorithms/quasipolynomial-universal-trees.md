# Quasipolynomial universal trees

For all positive integers $n$ and $h$ there is an $(n, h)$-[universal tree](universal-trees.md) of size $f(n, h)$, where $f(n, 0) = 1$ for $n \ge 1$,
$f(0, h) = 0$ for $h \ge 1$ (the value of an empty side in the recurrence, not a tree), and
$f(n, h) = f(n, h - 1) + f(\lfloor n/2 \rfloor, h) + f(n - 1 - \lfloor n/2 \rfloor, h)$ for $n, h \ge 1$. Moreover

$$f(n, h) \le n \binom{h - 1 + \lfloor \log_2 n \rfloor}{\lfloor \log_2 n \rfloor},$$

which is quasipolynomial in $n$ and $h$, and polynomial in $n$ when $h = O(\log n)$ (Jurdziński and Lazić).

## Depends on

- [Universal trees](universal-trees.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Theorem 2.7 and its proof, and the bibliographic references of Chapter 2, which credit the succinct progress measures to Jurdziński and Lazić.
- M. Jurdziński and R. Lazić, "Succinct progress measures for solving parity games", *Proceedings of the 32nd IEEE LICS*, 2017, arXiv:1702.05051v3: Sections 2 and 3 (ordered tree codings and the succinct tree coding result).
