# Min-isolation of proof trees in semi-unbounded circuits

Let $C$ be a semi-unbounded circuit with $s$ gates and $w$ wires, and fix an input $x$. Assign a positive integer weight to every wire and define the weight of a proof tree (in the unfolding, as on the linked page) as the sum of the weights of the wire occurrences it uses, counted with multiplicity. The weighting is *min-unique on $x$* if every gate that is true on $x$ has exactly one proof tree of minimum weight.

If the $w$ wire weights are chosen independently and uniformly from $\{1,\dots,M\}$, then for the fixed input $x$

$$\Pr[\text{the weighting is not min-unique on } x] \le \frac{s\,w}{M};$$

for $M\ge4sw$ (for instance $M=4s^3$ when there are no parallel wires, so that $w\le s^2$) the weighting is min-unique on $x$ with probability at least $3/4$. The guarantee is per input: one weighting need not work for all inputs. Consequently there is a *list* of $\max(n,1)$ such weightings, for an $n$-input circuit, such that every input has a weighting in the list that is min-unique on it. If $C$ has depth $d$, every proof tree has at most $2^{d+1}$ wire occurrences, so minimum weights are at most $2^{d+1}M$; for polynomial size and logarithmic depth they have $O(\log n)$ bits.

## Proof sketch

For a wire $e$ and a gate $g$, let $\mathrm{Bad}(e,g)$ be the event that $e$ occurs in one minimum-weight proof tree of $g$ and not in another. If some true gate has two minimum-weight proof trees, take a lowest such gate $g$: its children have unique minimum trees, so $g$ is an OR gate whose two minimum trees enter through different wires $e_1\ne e_2$, and $e_1$ cannot occur below $g$, so $\mathrm{Bad}(e_1,g)$ holds. Fix all weights except that of $e$: the minimum weight of trees of $g$ using $e$ is a strictly increasing function of $w(e)$ (each such tree uses $e$ at least once), while the minimum over trees avoiding $e$ does not depend on $w(e)$, so at most one value of $w(e)$ makes $\mathrm{Bad}(e,g)$ occur, which has probability at most $1/M$. A union bound over the $s\,w$ pairs $(g,e)$ gives the bound. For the list, $m=\max(n,1)$ independent weightings all fail on a fixed input with probability at most $4^{-m}$, and $2^n\cdot4^{-m}<1$ (it is $1/4$ for $n=0$ and $2^{-n}$ for $n\ge1$).

## Depends on

- [Layered semi-unbounded circuits and proof trees](semi-unbounded-circuits-and-proof-trees.md)

## Sources

- Klaus Reinhardt, Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing, 2000 (Section 3: the definition of certificates and their weights, and Lemma 3.2 with its proof, which uses weights in $[1,4n^{3k}]$ for a circuit of size $n^k$, probability at least $3/4$ for each fixed input, and a list of $n$ weight functions).
