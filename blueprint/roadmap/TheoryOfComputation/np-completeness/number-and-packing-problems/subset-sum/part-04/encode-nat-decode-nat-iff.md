# Canonical binary strings are those not ending in zero

For every bit string $p$, encoding
in binary (least significant bit first) the natural number that $p$ decodes to gives back $p$ if
and only if the trailing-zero test, started with no trailing zero, reports that $p$ does not end
in $0$; that is, $p$ is empty or its last bit is $1$.
