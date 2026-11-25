# Modulus amplification for parity satisfiability

Write $\#(\varphi)$ for the number of satisfying assignments of a Boolean formula $\varphi$. There is a deterministic polynomial-time transformation $T$ such that, for every formula $\psi$ and every $m \ge 1$ given in unary, $T(\psi, 1^m)$ is an unquantified Boolean formula $\psi^*$ with

- $\#(\psi^*) \equiv -1 \pmod{2^{m+1}}$ if $\#(\psi)$ is odd, and
- $\#(\psi^*) \equiv 0 \pmod{2^{m+1}}$ if $\#(\psi)$ is even.

Combined with the [randomized reduction from the polynomial hierarchy to parity satisfiability](randomized-reduction-from-ph-to-parity-sat.md), this lets a single call to a $\#\mathrm{SAT}$ oracle replace the random choices: the sum of $\#(T(\cdot))$ over all random strings is $0$ modulo $2^{m+1}$ for inputs outside the language and nonzero for inputs in it. This is the second step of [Toda's theorem](toda.md).

**Proof.** There are formula operations $\varphi + \tau$ and $\varphi \cdot \tau$, with size linear in the sizes of $\varphi$ and $\tau$, such that $\#(\varphi + \tau) = \#(\varphi) + \#(\tau)$ and $\#(\varphi \cdot \tau) = \#(\varphi)\#(\tau)$. Let $\psi_0 = \psi$ and $\psi_{i+1} = 4\psi_i^3 + 3\psi_i^4$, so that $\#(\psi_{i+1}) = 4\#(\psi_i)^3 + 3\#(\psi_i)^4$. For every integer $a$ and $i \ge 0$, if $a \equiv -1 \pmod{2^{2^i}}$ then $4a^3 + 3a^4 \equiv -1 \pmod{2^{2^{i+1}}}$, and if $a \equiv 0 \pmod{2^{2^i}}$ then $4a^3 + 3a^4 \equiv 0 \pmod{2^{2^{i+1}}}$. An odd count is $-1$ and an even count is $0$ modulo $2 = 2^{2^0}$. So $\psi^* = \psi_{\lceil \log_2(m+1) \rceil}$ has the stated residues, and $\lceil \log_2(m+1) \rceil$ rounds of a constant-factor blow-up keep its size polynomial in $|\psi|$ and $m$.

## Depends on

- [The counting class $\#P$](../complexity-classes/time-and-space-complexity-classes/sharp-p.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009; web draft of January 2007, <https://theory.cs.princeton.edu/complexity/book.pdf>, Section 9.3.3: Lemma 9.19 and its proof, and the proof of Theorem 9.11 from Lemmas 9.18 and 9.19 (pp. 9.13–9.14).
- S. Toda, "PP is as hard as the polynomial-time hierarchy", *SIAM Journal on Computing* 20(5):865–877, 1991.
