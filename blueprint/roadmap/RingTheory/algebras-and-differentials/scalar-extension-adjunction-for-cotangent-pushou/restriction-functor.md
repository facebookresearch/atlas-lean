# Restriction along the ground algebra map

For commutative rings `k : Type u`, `K : Type w` with `Algebra k K`, `restrictionFunctor k K :
CommAlgCat.{max u v w} K → CommAlgCat.{max u v w} k` restricts scalars along `algebraMap k K`.
Each algebra retains its carrier and underlying ring.
