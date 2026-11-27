# The finite oracle evaluator is primitive recursive

Oracle codes are the finite programs built from $\mathtt{zero}$, $\mathtt{succ}$, $\mathtt{left}$, $\mathtt{right}$ and $\mathtt{oracle}$ by the constructors $\mathtt{pair}$, $\mathtt{comp}$, $\mathtt{prec}$ and $\mathtt{rfind}$; they are numbered by an injective Gödel numbering into $\mathbb{N}$, whose set of valid numbers is primitive recursive and whose decoding is primitive recursive on valid numbers; not every natural number is the number of a program (for instance $1$ is not). For an oracle $o$ assigning to each natural number either a natural number or no value, the fuel-bounded evaluator $E^o_k(c, n)$ returns a natural number or fails: $E^o_0(c, n)$ always fails; $E^o_{k+1}(c, n)$ fails if $n > k$, and otherwise, writing $n = \langle a, m \rangle$, evaluates $c$ as a partial recursive program (constant zero, successor, the two unpairing projections, pairing, composition, primitive recursion and unbounded search, with sub-evaluations at fuel $k+1$ or, for the recursive call of $\mathtt{prec}$ and $\mathtt{rfind}$, at fuel $k$), where $\mathtt{oracle}$ returns $o(n)$ and fails if $o$ has no value at $n$.

The following holds: if $o : \mathbb{N} \to \mathbb{N} \cup \{\text{none}\}$ is primitive recursive, then the map

$$(k, c, n) \longmapsto E^o_k(c, n)$$

is primitive recursive, as a function of the fuel $k$, the oracle code $c$ and the input $n$.

## Sources

- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2.
- H. Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6.
