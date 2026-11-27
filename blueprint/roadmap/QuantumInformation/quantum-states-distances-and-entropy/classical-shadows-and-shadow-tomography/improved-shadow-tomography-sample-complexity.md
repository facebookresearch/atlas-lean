# Bădescu-O'Donnell: shadow tomography with log-squared dependence on the number of observables

Shadow tomography of $M$ observables on a $D$-dimensional state can be performed with

$$
N = \tilde O\!\left( \frac{\log^2 M \cdot \log D}{\varepsilon^4} \right)
$$

copies; the same bound holds for quantum hypothesis selection among $M$ states.

## Proof sketch

Replace the search step of Aaronson's algorithm by quantum threshold search with $O(\log^2 M/\varepsilon^2)$ copies per round and combine with the online learner with $O(\log D/\varepsilon^2)$ mistakes.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)

## Proof depends on

- [Aaronson: shadow tomography with polylogarithmically many copies](aaronson-shadow-tomography-theorem.md)
- [Quantum threshold search](quantum-threshold-search.md)

## Sources

- Costin Badescu, Ryan O'Donnell, "Improved quantum data analysis", STOC (2021), TheoretiCS (2024); arXiv:2011.10908.
