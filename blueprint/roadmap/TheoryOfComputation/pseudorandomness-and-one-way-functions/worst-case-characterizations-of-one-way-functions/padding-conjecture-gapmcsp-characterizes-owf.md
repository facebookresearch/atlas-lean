# Under the padding conjecture, worst-case hardness of approximating MCSP within 2^{(1−ε)n} characterizes one-way functions

Assume the Meta-Complexity Padding Conjecture. Then the following are equivalent:

1. There is a one-way function secure against randomized polynomial-time algorithms infinitely often.
2. For every constant $\epsilon>0$, no randomized polynomial-time algorithm approximates the circuit complexity of a given truth table of length $2^n$ within a factor $2^{(1-\epsilon)n}$.
3. For every polynomial $p$, no randomized polynomial-time algorithm distinguishes $q^t(x)\le s$ from $q^{p(t)}(x)>p(s)$ on inputs $(x,1^t,1^s)$ with $t\ge|x|$, where $q^t(x)=-\log Q^t(x)$ and $Q^t(x)$ is the $t$-time-bounded universal a priori probability of $x$.
4. For every polynomial $p$, no randomized polynomial-time algorithm distinguishes $\mathrm{rK}^t(x)\le s$ from $\mathrm{rK}^{p(t)}(x)>p(s)$ on inputs $(x,1^t,1^s)$ with $t\ge|x|$.
5. There is a pseudorandom generator secure against randomized polynomial-time algorithms infinitely often.
6. For every constant $\epsilon>0$ there is a hitting set generator $H_n:\{0,1\}^{n^{\epsilon}}\to\{0,1\}^n$ secure against randomized polynomial-time algorithms infinitely often.

Thus the conjecture closes the gap between avoiding hitting set generators (equivalent to worst-case approximation of time-bounded complexity) and breaking pseudorandom generators (equivalent to error-prone average-case hardness of time-bounded complexity).

## Proof sketch

Items 1, 5 and 6 are related by standard constructions (a pseudorandom generator is a hitting set generator, and one-way functions give pseudorandom generators). Items 2 to 4 are worst-case hardness statements equivalent to security of a hitting set generator. The new direction, from a secure hitting set generator to a one-way function, uses the padding conjecture: the size-expanding reduction maps the worst-case gap problem to instances of $\mathrm{dpK}$ that are so large that errorless average-case algorithms and error-prone ones become interchangeable, so worst-case hardness of approximating time-bounded complexity translates into the error-prone average-case hardness that characterizes one-way functions.

## Depends on

- [The Meta-Complexity Padding Conjecture](meta-complexity-padding-conjecture.md)
- [Hitting set generators and algorithms that avoid them](hitting-set-generators-and-avoidance.md)
- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Hirahara: one-way functions exist iff approximating distributional Kolmogorov complexity is NP-hard and NP is worst-case hard](hirahara-owf-iff-np-hardness-of-dk.md)
- [Pseudorandom generators exist if and only if one-way functions exist](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Shuichi Hirahara, "Capturing One-Way Functions via NP-Hardness of Meta-Complexity", STOC (2023), ECCC TR23-037.
