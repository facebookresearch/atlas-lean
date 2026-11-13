# Decoding oracle codes

The computable decoder for the Gödel numbering of oracle codes
sends a natural number $n$ to the result of the fuel-indexed decoder with fuel $n + 1$, tag $n_1$
and payload $n_2$, where $(n_1, n_2)$ is the unpairing of $n$; the result is either an oracle code
or undefined. The fuel $n + 1$ is more than enough, since the depth of an oracle code is at most
its code number.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings; decoding).
