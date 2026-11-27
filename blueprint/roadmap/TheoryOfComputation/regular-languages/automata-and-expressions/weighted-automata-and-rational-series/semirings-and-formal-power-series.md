# Semirings and formal power series on a free monoid

A *semiring* $(S, +, \cdot, 0, 1)$ has a commutative monoid $(S, +, 0)$ and a monoid $(S, \cdot, 1)$, multiplication distributes over addition on
both sides, and $0 \cdot s = s \cdot 0 = 0$; examples are the Boolean semiring $\mathbb{B} = (\{0, 1\}, \vee, \wedge, 0, 1)$, $(\mathbb{N}, +, \cdot, 0, 1)$ and the
max-plus semiring $(\mathbb{N} \cup \{-\infty\}, \max, +, -\infty, 0)$. For a finite alphabet $\Sigma$, a *series* is a map $r : \Sigma^* \to S$, with
$(r, w) = r(w)$; $S\langle\langle \Sigma^* \rangle\rangle$ is the set of series. Its *support* is $\mathrm{supp}(r) = \{w : (r, w) \ne 0\}$, and the
*characteristic series* $1_L$ of a language $L$ takes the value $1$ on $L$ and $0$ elsewhere. Series are added pointwise, and the
*Cauchy product* is $(r_1 \cdot r_2, w) = \sum_{w = uv} (r_1, u) (r_2, v)$, which makes $S\langle\langle \Sigma^* \rangle\rangle$ a semiring with unit
$1_{\{\varepsilon\}}$. A series $r$ is *proper* if $(r, \varepsilon) = 0$; then $(r^n, w) = 0$ for $n > |w|$, and its *iteration*
$r^* = \sum_{n \ge 0} r^n$ is defined. A *monomial* is a series $s a$ with $s \in S$ and $a \in \Sigma \cup \{\varepsilon\}$, taking the value $s$ on $a$
and $0$ elsewhere. The *Hadamard product* $r_1 \odot r_2$ multiplies pointwise.

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Definition 2.2 (semirings), the paragraph after Definition 2.3 (series), Definition 2.4 (supports and characteristic series) and Section 4 (Cauchy product, proper series, iteration, monomials).
