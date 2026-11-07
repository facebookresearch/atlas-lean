# Statistical Mechanics

Statistical mechanics studies lattice models of interacting spins and bonds through Gibbs measures, partition functions, correlation inequalities, and phase transitions.

Most of the subject follows the Ising model from a finite graph to the infinite lattice. On a finite graph the
[Lee–Yang circle theorem](spin-models/lee-yang-circle-theorem/README.md) puts the zeros of the ferromagnetic partition
function, as a polynomial in the fugacity $e^{-2\beta h}$ of the external field $h$, on the unit circle, and the
[Griffiths](correlation-inequalities/griffiths-inequalities/README.md) and
[Griffiths–Hurst–Sherman](correlation-inequalities/griffiths-hurst-sherman-inequality/README.md) inequalities control
how spins correlate. On the lattice, the
[Peierls argument](gibbs-states-and-phase-transitions/peierls-argument-for-the-ising-model/README.md) gives long-range
order at low temperature, the ordered half of the
[phase transition](gibbs-states-and-phase-transitions/phase-transition-of-the-ising-model/README.md).

The two-dimensional model is exactly solvable.
[Kramers–Wannier duality](exact-solutions/kramers-wannier-duality/README.md) exchanges high and low temperature.
[Kac–Ward matrices](exact-solutions/kac-ward-matrices/README.md) and
[Sherman's loop cancellations](exact-solutions/sherman-s-loop-cancellations-and-product-formula/README.md) relate
Kac–Ward determinants to sums over closed walks, the
[spin Kac–Ward identities](exact-solutions/spin-kac-ward-identities/README.md) express the partition function on the
torus through four such determinants, and
[Onsager's solution](exact-solutions/onsager-s-solution-of-the-two-dimensional-ising/README.md) computes the free energy
per site in the infinite-volume limit.

The largest field is the [random-cluster model](random-cluster-model/README.md). The
[Edwards–Sokal coupling](random-cluster-model/edwards-sokal-coupling-and-the-fk-representation/README.md) couples Potts
and Ising spins with random subgraphs, turning spin correlations into connection probabilities, and from measures on
finite graphs the field builds infinite-volume measures, the free energy and the critical point.
[Random currents and the switching lemma](random-currents-and-sharpness/random-currents-and-the-switching-lemma/README.md)
lead to the [sharpness of the phase transition](random-currents-and-sharpness/sharpness-of-the-phase-transition-for-the-ising/README.md)
for the Ising model.

- [Lattice spin models](spin-models/README.md)
- [Correlation inequalities for spin systems](correlation-inequalities/README.md)
- [Gibbs states and phase transitions](gibbs-states-and-phase-transitions/README.md)
- [Exact solutions and duality](exact-solutions/README.md)
- [Random currents and sharpness](random-currents-and-sharpness/README.md)
- [Random-cluster model](random-cluster-model/README.md)
