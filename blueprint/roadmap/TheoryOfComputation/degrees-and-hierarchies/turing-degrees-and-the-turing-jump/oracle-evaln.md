# Fuel-indexed evaluation of oracle codes

Write $\langle a, b \rangle$ for the pairing of
natural numbers. For an oracle $o$ assigning to each natural number a natural number or no
value, a fuel $k$, an oracle code $c$ and an input $n$, the evaluator $E_k(c, n)$ returns a
natural number or fails. $E_0(c, n)$ always fails. $E_{k+1}(c, n)$ fails if $n > k$;
otherwise, with $n = \langle a, m \rangle$:

- $\mathtt{zero}$ returns $0$, $\mathtt{succ}$ returns $n + 1$, $\mathtt{left}$ returns $a$ and
  $\mathtt{right}$ returns $m$;
- $\mathtt{pair}(f, g)$ returns $\langle E_{k+1}(f, n), E_{k+1}(g, n) \rangle$;
- $\mathtt{comp}(f, g)$ returns $E_{k+1}(f, x)$ where $x = E_{k+1}(g, n)$;
- $\mathtt{prec}(f, g)$ returns $E_{k+1}(f, a)$ if $m = 0$, and if $m = y + 1$ it returns
  $E_{k+1}(g, \langle a, \langle y, i \rangle \rangle)$ where $i = E_k(\mathtt{prec}(f, g),
  \langle a, y \rangle)$;
- $\mathtt{rfind}(f)$ computes $x = E_{k+1}(f, \langle a, m \rangle)$ and returns $m$ if $x = 0$,
  and $E_k(\mathtt{rfind}(f), \langle a, m + 1 \rangle)$ otherwise;
- $\mathtt{oracle}$ returns $o(n)$, failing if $o$ has no value at $n$.

In every case the result fails if any evaluation it uses fails.

## Sources

- Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2 (oracle computations).
