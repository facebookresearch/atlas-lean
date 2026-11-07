# Parsing a list of booleans into self-delimiting blocks

Given a list of booleans $s$, this
repeatedly parses one self-delimiting block from the front of $s$ until $s$ is used up, allowing
at most as many blocks as the length of $s$, and returns the list of payloads in order. It fails
if some block fails to parse. The bound never binds, since every block uses at least one bit.
So the parse succeeds exactly when $s$ is a concatenation of self-delimiting blocks.
