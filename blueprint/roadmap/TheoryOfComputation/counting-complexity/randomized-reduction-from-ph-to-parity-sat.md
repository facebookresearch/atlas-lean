# Randomized reduction from the polynomial hierarchy to parity satisfiability

For a Boolean formula $\varphi$ on $n$ variables, write $\bigoplus_{x \in \{0,1\}^n} \varphi(x)$ for the statement that the number of satisfying assignments of $\varphi$ is odd. The language $\oplus\mathrm{SAT}$ consists of the true statements $\bigoplus_{x} \varphi(x)$ with $\varphi$ an unquantified Boolean formula, not necessarily in conjunctive normal form.

For every constant $c \in \mathbb{N}$ there is a probabilistic polynomial-time algorithm $A$ such that, for every quantified Boolean formula $\psi$ with $c$ levels of alternating quantifiers:

- if $\psi$ is true, then $\Pr[A(\psi) \in \oplus\mathrm{SAT}] \ge 2/3$;
- if $\psi$ is false, then $\Pr[A(\psi) \in \oplus\mathrm{SAT}] = 0$.

Since membership in a language of the polynomial hierarchy reduces in polynomial time to the truth of a quantified Boolean formula with a constant number of alternations, every language in $\mathsf{PH}$ reduces to $\oplus\mathrm{SAT}$ by a randomized polynomial-time reduction with one-sided error. This is the first step of Toda's theorem.

The proof removes one $\exists$ or $\forall$ quantifier at a time, replacing it by a parity quantifier. Each Valiant–Vazirani run isolates a given nonempty witness set with probability at least $1/(8n)$, so each step uses $t = O(n(\ell + \log c))$ independent runs, for instance $100\,c\,\ell\,n$, so that every nonempty set of witnesses is isolated by some run except with probability less than $2^{-\ell}/(10c)$. It then recombines the runs with the formula operations $\varphi \cdot \psi$ and $\varphi + \psi$, which multiply and add the numbers of satisfying assignments, using the parity identities for conjunction, negation and disjunction. A false formula stays false at every step, and a true formula stays true except with probability at most $1/(10c)$ per step.

## Depends on

- [The polynomial hierarchy](../complexity-classes/time-and-space-complexity-classes/ph.md)

## Proof depends on

- [Valiant-Vazirani: SAT reduces to UniqueSAT](../randomized-and-quantum-complexity/valiant-vazirani-theorem/valiant-vazirani.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009; web draft of January 2007, <https://theory.cs.princeton.edu/complexity/book.pdf>, Section 9.3: Definition 9.14 ($\oplus\mathrm{SAT}$), Theorem 9.15 (Valiant–Vazirani), Lemma 9.18 and its proof (pp. 9.11–9.13).
- S. Toda, "PP is as hard as the polynomial-time hierarchy", *SIAM Journal on Computing* 20(5):865–877, 1991.
