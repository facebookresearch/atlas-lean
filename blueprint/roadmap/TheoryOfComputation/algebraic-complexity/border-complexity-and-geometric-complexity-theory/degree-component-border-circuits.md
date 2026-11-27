# Degree-component border circuits

For a finite variable type, a field $F$, a degree $d$, and a natural $s$, extend the target polynomial from $F$ to an algebraic closure $\overline F$ and keep only its coefficients at monomials of total degree exactly $d$. The target has degree-component border cost at most $s$ when this vector belongs to the Zariski closure of coefficient vectors, in that same degree, of outputs of exact arithmetic circuits over $\overline F$ with at most $s$ binary addition, subtraction or multiplication gates. Inputs/constants and output selection are free; circuits may share gates. Their output polynomials may have other degrees. Equivalently, every polynomial in the coefficient coordinates vanishing on the attainable vectors vanishes on the target vector. The degree-component border size is the least such $s$.

## Depends on

- Exact formal polynomial arithmetic circuits and degree-$d$ coefficient projection.

## Expansion

Separate the circuit-size carrier and coefficient projection from the Zariski closure, and show exact realization after scalar extension bounds border size at the same cost. Do not use coefficientwise convergence in an unspecified metric or require homogeneous circuits.

## Sources

- OpenAI, [Coefficient vectors, closure and minimum size](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Computability/BorderVNP/Model.lean#L18-L129) and [Degree-component model predicate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Hierarchy/DegreeBorder.lean#L16-L35).
