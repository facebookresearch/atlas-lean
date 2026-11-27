# Forced variables with respect to an order

Let $\varphi$ be a CNF formula on variables $V$, $\pi$ a linear order of $V$ and $x$ a satisfying assignment. A variable $v$ is *forced* on $x$ with respect to $\pi$ if some clause of $\varphi$ contains the literal of $v$ that is true under $x$, and all other literals of that clause are on variables preceding $v$ in $\pi$ and are false under $x$. A variable $v$ is *critical* (for an isolated solution $x$ in direction $v$) if flipping $v$ in $x$ falsifies $\varphi$; every critical variable is witnessed by a clause in which $v$'s literal is the only true one.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science 1999(11), 1999, Section 2 (Lemmas 1 and 2).
