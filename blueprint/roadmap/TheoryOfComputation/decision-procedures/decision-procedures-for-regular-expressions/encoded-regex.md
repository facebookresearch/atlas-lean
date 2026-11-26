# Encoded regular expressions

An encoded regular expression over an alphabet $\alpha$ is a
list of regular-expression nodes, each a constant ($0$, $1$ or a letter) or an operator (sum,
concatenation or star) whose arguments are node indices; the last node is the root. Any list is
allowed: in the semantics, an argument that is not the index of an earlier node reads as $0$,
and the empty list denotes $0$.
