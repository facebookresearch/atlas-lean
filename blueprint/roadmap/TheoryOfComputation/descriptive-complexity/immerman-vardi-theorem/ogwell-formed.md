# Well-formed FO + LFP formulas

Let $e$ assign to each relation symbol (a natural number)
either an arity or nothing. Whether a first-order formula with least fixed points over ordered
graphs is well-formed relative to $e$ is defined by recursion on the formula. An equality of two
variables is well-formed. An atomic formula $R(x_1, \dots, x_k)$ is well-formed when $k = a$ if
$e(R) = a$; when $k = 2$ if $e$ assigns nothing to $R$ and $R$ is $0$ (the order) or $1$ (the edge
relation); and always otherwise. A negation or an existential quantification is well-formed when
its body is, and a conjunction or a disjunction when both of its parts are. A least-fixed-point
formula that binds the symbol $R$ with arity $a$, has body $\varphi$ and is applied to the
variables $y_1, \dots, y_k$ is well-formed when $R \ge 2$, $k = a$, and $\varphi$ is well-formed
relative to the assignment that agrees with $e$ except that it gives $R$ the arity $a$.
