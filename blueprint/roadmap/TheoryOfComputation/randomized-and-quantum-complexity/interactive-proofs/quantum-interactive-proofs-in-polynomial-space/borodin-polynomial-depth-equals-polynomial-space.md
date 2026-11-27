# Borodin: NC(poly) = PSPACE

$\mathrm{NC}(\mathrm{poly}) = \mathrm{PSPACE}$. More generally, for space-constructible $s(n) \ge \log n$, space-uniform bounded fan-in circuits of depth $O(s(n))$ can be evaluated in space $O(s(n))$, and $\mathrm{NSPACE}(s(n)) \subseteq$ uniform depth $O(s(n)^2)$.

## Proof sketch

A depth-$d$ circuit is evaluated by a depth-first recursion of depth $d$ storing $O(1)$ bits per level plus gate names, using space $O(d + \log \mathrm{size})$. Conversely the configuration graph of a space-$s$ machine has $2^{O(s)}$ nodes, and reachability is computed by repeated Boolean matrix squaring in depth $O(s^2)$.

## Depends on

- [The class NC(poly) of polynomial-depth bounded fan-in circuit families](polynomial-depth-circuit-class-nc-poly.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- Allan Borodin, "On relating time and space to size and depth", SIAM Journal on Computing 6(4) (1977).
