# Dense CNF-SAT certificate check

For bit strings $w$ (the encoded formula) and $y$ (the
certificate), the check of $y$ against $w$ is the Boolean result of the verifier's left-to-right
scan of the formula bits $w$, started with $y$ as the assignment bits not yet used by the current
clause, no used bits, and the current clause not yet satisfied.
