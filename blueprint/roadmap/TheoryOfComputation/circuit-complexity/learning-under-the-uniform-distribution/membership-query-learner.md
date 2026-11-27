# Randomized membership-query learner as a family of decision trees

A learner with membership queries may ask for $f(x)$ at points $x$ of its choice. With its random seed $\omega$ fixed, it is a decision tree whose internal nodes are labelled by points of $\{0,1\}^n$ (a query of $x$ branches on $f(x)$) and whose leaves are hypotheses; running it on the truth table of $f$ returns a hypothesis $A_\omega(f)$. A randomized membership-query learner is a family of such trees indexed by seeds drawn from a distribution $\mu$. It makes at most $q$ queries if every tree has depth at most $q$, and it learns $C$ with error $\varepsilon$ and confidence $1 - \delta$ if for every $f \in C$, $\Pr_{\omega \sim \mu}[\mathrm{err}(f, A_\omega(f)) > \varepsilon] \le \delta$. A non-adaptive learner chooses its query points from the seed alone. Querying uniformly random points simulates learning from uniform random examples, and the two models then learn the same classes.

## Depends on

- [Learning from uniform random examples](learning-from-uniform-random-examples.md)
- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)

## Sources

- Dana Angluin, "Queries and Concept Learning", Machine Learning, 1988.
- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
