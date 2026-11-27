# Horn-definable relations are exactly the AND-closed relations

A Boolean relation $R \subseteq \{0,1\}^I$ on a finite coordinate set $I$ (including empty and nullary relations) is definable by a conjunction of Horn clauses (clauses with at most one positive literal) over the variables $I$, without auxiliary variables, if and only if binary conjunction $\wedge$ is a polymorphism of $R$, i.e. $R$ is closed under coordinatewise AND. Dually, $R$ is definable by dual-Horn clauses (at most one negative literal) iff it is closed under coordinatewise OR.

## Proof sketch

Models of a Horn clause are closed under AND since a Horn clause is satisfied by $x \wedge y$ whenever by both. Conversely, for an AND-closed $R$ and a tuple $t \notin R$, the AND of all members of $R$ above $t$ on the coordinates where $t$ is $1$ yields a separating Horn clause excluding $t$ but no member of $R$; conjoin these clauses over all $t \notin R$.

## Depends on

- [Polymorphisms of relations](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/boolean-clones-and-post-lattice/polymorphisms-of-relations.md)
- [Horn formula](../../../../Logic/propositional-logic/horn-satisfiability/is-horn.md)

## Sources

- M. Bodirsky, Graph Homomorphisms and Universal Algebra, lecture notes, TU Dresden.
- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
