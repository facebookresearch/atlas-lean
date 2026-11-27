# Runs of the product DFA

Let $S$ be a sequential transducer and $M$ a DFA over the
output alphabet of $S$. For every input word $x$, state $q$ of $S$ and state $r$ of $M$, the
product DFA of $S$ and $M$, started in $(q, r)$ and run on $x$, ends in the state $(q', r')$,
where $q'$ is the final state of the run of $S$ from $q$ on $x$ and $r'$ is the state that $M$
reaches from $r$ on the output word of that run.
