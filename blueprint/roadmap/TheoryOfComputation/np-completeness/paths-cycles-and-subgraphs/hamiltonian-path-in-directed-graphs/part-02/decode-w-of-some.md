# Decoding peels off the first number

If reading a unary number from the front of a list
$w$ of bits returns $v$ with remaining bits $r$, that is, $w$ is $v$ copies of true, then false,
then $r$, then the witness decoder succeeds on $w$ exactly when it succeeds on $r$, and its
result on $w$ is $v$ followed by its result on $r$.
