# Single-tape halting many-one reduces to string rewriting reachability

Let $M$ be a
single-tape Turing machine with finitely many states and tape symbols. Then the set of inputs on
which $M$ halts is many-one reducible to the set of instances $(R, x, y)$, where $R$ is a list of
rules and $x$, $y$ are words over the symbols of the rewriting system simulating $M$, such that
every rule of $R$ has a nonempty left side and a nonempty right side and $x$ rewrites to $y$ in
zero or more steps of $R$.
