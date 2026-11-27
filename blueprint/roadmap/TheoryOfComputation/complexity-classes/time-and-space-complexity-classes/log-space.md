# Deterministic logarithmic space

The class $\mathsf{L}$ consists of the decision problems
$L$ for which there is a constant $c \in \mathbb{N}$ such that the language of $L$ lies in
$\mathrm{DSPACE}(s)$ for $s(n) = c \lfloor \log_2(n + 1) \rfloor + c$, the class of languages
decided by a multi-tape Turing machine with binary alphabet and finitely many states, within
some time bound, visiting at most $c_1 s(n) + c_2$ work-tape cells on inputs of length $n$ for
some constants $c_1$ and $c_2$.
