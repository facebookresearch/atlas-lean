# Boolean constraint languages and CSP(Γ)

A *Boolean constraint language* $\Gamma$ is a set of relation symbols, each with an arity $r(R) \in \mathbb{N}$ and an interpretation $R^\Gamma \subseteq \{0,1\}^{r(R)}$, fixed independently of any instance. An instance of $\mathrm{CSP}(\Gamma)$ is a finite list of constraints $R(v_1,\dots,v_{r(R)})$ over variables $V$ (repetitions allowed); it is satisfiable if some assignment $\sigma : V \to \{0,1\}$ puts $(\sigma v_1,\dots,\sigma v_r)$ into $R^\Gamma$ for every constraint. For example 3-SAT is $\mathrm{CSP}(\Gamma)$ for the eight width-three clause relations, and 1-in-3-SAT is $\mathrm{CSP}(\{\{100,010,001\}\})$.

## Sources

- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009): Section 3.
