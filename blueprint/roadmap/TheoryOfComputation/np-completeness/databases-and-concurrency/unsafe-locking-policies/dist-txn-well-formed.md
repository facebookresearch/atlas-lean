# Distributed transaction is well-formed in UNSAFE LOCKING POLICY for two distributed transactions

In UNSAFE LOCKING POLICY for two distributed transactions, a distributed transaction, with step list $T$ and list of precedence pairs $P$, is well-formed for a list of sites when:

- $T$ is a well-formed transaction of UNSAFE LOCKING POLICY: every step is a lock, update or unlock, and for each variable $x$, the transaction either has no step on $x$, or has exactly one $\mathrm{lock}(x)$ and exactly one $\mathrm{unlock}(x)$, the $\mathrm{lock}(x)$ before the $\mathrm{unlock}(x)$, with every $\mathrm{update}(x)$ of the transaction (there may be any number of them, including none) strictly between the two;
- every variable $x$ of a step of $T$ has a site, that is, $x$ is less than the length of the list of sites;
- every pair $(p, q)$ in $P$ satisfies $p < q < |T|$, so it names two steps of $T$, the first one listed first;
- $P$ is transitively closed: whenever $(p, q)$ and $(q, r)$ are in $P$, so is $(p, r)$;
- for any positions $p < q$ of $T$ whose steps are on variables with the same site, the pair $(p, q)$ is in $P$.

Under these conditions $P$ lists a strict partial order on the steps of $T$, consistent with the order of $T$, that totally orders the steps of each site.
