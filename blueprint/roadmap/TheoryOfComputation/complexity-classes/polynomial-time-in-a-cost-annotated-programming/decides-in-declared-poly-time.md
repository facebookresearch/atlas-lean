# Declared polynomial time for timed deciders

Let $f$ be a timed function that maps each
list $x$ of Booleans to a Boolean $f(x)$ together with a declared time $t_f(x) \in \mathbb{N}$.
Then $f$ decides in declared polynomial time when there is a polynomial $p$ with natural-number
coefficients such that $t_f(x) \le p(|x|)$ for every list $x$ of Booleans, where $|x|$ is the
length of $x$.

This constrains only the trusted time annotation: it implies neither that $f$ is computable in
any machine model nor that $f$ is related to any particular decision problem.
