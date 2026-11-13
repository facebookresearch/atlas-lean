# Parsing one self-delimiting block

Write booleans as bits, with true as $1$ and false as
$0$. Reading a list of bits from the front, a $0$ ends the block, and a $1$ followed by a bit $b$
contributes $b$ to the payload. The result is the payload together with the rest of the list
after the terminating $0$. Parsing fails if the list runs out before a terminating $0$ is read.
