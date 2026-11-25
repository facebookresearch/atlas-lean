# Postfix reader step

One step of the postfix reader: push a variable, or replace the top two subexpressions $a, b$ (in written order) by $c(a, b)$; failure records a stack underflow or an unknown token kind.
