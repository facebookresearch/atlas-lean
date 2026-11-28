# Boolean relations

A relation is stored as a pair of a natural arity $k$ and a list of Boolean lists. The list need not consist of rows of length $k$: for $(1, [[\,]])$ the stored row has length $0$. The fixed-sequence predicates read the relation through its length-$k$ rows only: a tuple $t$ satisfies the relation when $[t(0), \dots, t(k-1)]$ is a listed row, so $(1, [[\,]])$ is satisfied by no tuple. That every row has length $k$ is required by the [well-formedness of a sequence of relations](relations-well-formed.md).
