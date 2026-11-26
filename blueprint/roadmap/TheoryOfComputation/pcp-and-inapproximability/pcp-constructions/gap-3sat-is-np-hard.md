# Gap 3SAT is NP-hard

For a 3CNF formula $\varphi$, $\mathrm{val}(\varphi)$ is the largest fraction of clauses satisfied by an assignment. For $\rho \in (0, 1)$, *$\rho$-GAP 3SAT* asks, given $\varphi$,
whether $\varphi$ is satisfiable (a YES instance) or $\mathrm{val}(\varphi) \le \rho$ (a NO instance), with no requirement on other inputs. It is *NP-hard* if every
language $L \in \mathsf{NP}$ has a polynomial-time map $f$ sending members of $L$ to YES instances and non-members to NO instances.

**Theorem.** There is a constant $\rho \in (0, 1)$ such that $\rho$-GAP 3SAT is NP-hard. This is equivalent to the PCP theorem
$\mathsf{NP} = \mathsf{PCP}(O(\log n), O(1))$: NP-hardness of $\rho$-GAP 3SAT gives a verifier that reads the three variables of one random clause of $f(x)$, and conversely a PCP
verifier yields NP-hardness of a gap $q$CSP problem, which reduces to gap 3SAT with a constant loss in the gap.

## Proof depends on

- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Section 18.2: Definitions 18.9–18.11, Theorem 18.8 (restated as Lemma 18.15), Theorem 18.13 with the proofs of both directions, Remark 18.14 and Lemma 18.16.
