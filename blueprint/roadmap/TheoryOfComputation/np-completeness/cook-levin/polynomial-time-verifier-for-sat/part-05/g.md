# Input alphabet of the SAT verifier host

The alphabet $G$ of the host's input stack is the
pair alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$ of the dense SAT verifier.

In the encoding of a pair $(x, w)$, a formula bit $b$ is $\mathrm{inl}\ b$, the separator $\#$ is
$\mathrm{inr}\ \mathrm{none}$ and a certificate bit $b$ is $\mathrm{inr}\ (\mathrm{some}\ b)$.
