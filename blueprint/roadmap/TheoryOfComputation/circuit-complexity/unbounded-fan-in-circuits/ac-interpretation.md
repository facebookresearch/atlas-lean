# Boolean meaning of the unbounded fan-in basis

The Boolean interpretation of the unbounded fan-in signature matches the evaluation of flat circuits: a
constant outputs its value, negation flips its argument, $\mathrm{AND}_k$ and $\mathrm{OR}_k$ are the
conjunction and the disjunction of their $k$ arguments (true and false when $k = 0$), and
$\mathrm{MOD}_{m,k}$ outputs true exactly when $m \ne 0$ and the number of true arguments is divisible by
$m$.
