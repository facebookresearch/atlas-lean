# RECTILINEAR TRAVELING SALESMAN as a decision problem

The decision problem RECTILINEAR TRAVELING SALESMAN accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs $(P, B)$ of a list of encoded integer points and a bound, to an instance that is well-formed for GEOMETRIC TRAVELING SALESMAN (the points are nonempty and distinct and $B > 0$) and [feasible](rectilinear-traveling-salesman-feasible.md) for RECTILINEAR TRAVELING SALESMAN. It rejects every bitstring that does not decode to such an instance.
