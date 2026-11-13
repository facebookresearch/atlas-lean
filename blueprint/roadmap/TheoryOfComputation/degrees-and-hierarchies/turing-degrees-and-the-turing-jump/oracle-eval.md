# Evaluation of oracle codes

Let $o$ be an oracle that assigns to each natural number
either a natural number or no value, $c$ an oracle code and $n$ a natural number. The value of
$c$ on $n$ relative to $o$ is the value returned by the fuel-indexed evaluator of $c$ on $n$
relative to $o$ at the least fuel $k$ for which that evaluator returns a value; it is undefined
when there is no such $k$.

## Sources

- Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, §2 (oracle computations).
