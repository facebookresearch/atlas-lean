# Cooper's theorem

Let $\varphi(x)$ be a quantifier-free formula in negation normal form over the integers whose atoms are linear inequalities $i \le k x + \langle \vec k, \vec y \rangle$ and divisibility literals $d \mid i + k x + \langle \vec k, \vec y \rangle$ and $\neg(d \mid i + k x + \langle \vec k, \vec y \rangle)$, with integer coefficients, $d > 0$, other variables $\vec y$, and every coefficient $k$ of $x$ in $\{1, -1, 0\}$. Let

- $\delta$ be the least common multiple of the divisors $d$ of the divisibility literals in which $x$ occurs ($\delta = 1$ if there are none);
- $L$ be the set of *lower bounds* $l = i - \langle \vec k, \vec y \rangle$ of the atoms $i \le x + \langle \vec k, \vec y \rangle$;
- $\varphi_{-\infty}(j)$ be $\varphi$ with each atom $i \le x + \langle \vec k, \vec y \rangle$ replaced by $\bot$, each atom $i \le -x + \langle \vec k, \vec y \rangle$ by $\top$, and $x$ replaced by $j$ in the remaining atoms.

Then

$$\exists x \in \mathbb Z\ \varphi(x) \iff \bigvee_{j=0}^{\delta - 1} \varphi_{-\infty}(j) \ \vee\ \bigvee_{l \in L} \bigvee_{j=0}^{\delta - 1} \varphi(l + j).$$

An arbitrary linear formula is brought into this form as follows: let $m$ be the positive least common multiple of the nonzero coefficients of $x$ ($m = 1$ if there are none); multiply each atom whose coefficient $k$ of $x$ is nonzero by $m / |k|$, scaling the divisor of a divisibility literal too, so that the coefficient of $x$ becomes $\pm m$; leave atoms without $x$ unchanged; then replace $m x$ by $x$ and add the conjunct $m \mid x$. Applied to innermost quantifiers, this gives Cooper's quantifier elimination procedure for Presburger arithmetic. The theorem is due to D. C. Cooper (1972).

## Sources

- T. Nipkow, "Linear quantifier elimination", *Journal of Automated Reasoning* 45(2):189–212, 2010, <https://www21.in.tum.de/~nipkow/pubs/jar10.pdf>, Section 6.1 (atoms of linear integer arithmetic) and Section 6.4 (Cooper's theorem and its implementation), pp. 17 and 20–21 of the manuscript at this link.
