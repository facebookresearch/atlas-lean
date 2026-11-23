# A phase flip shifts the CSS codeword

For every $b$ and $w$, $Z^b |c_w\rangle = |c_{w + b}\rangle$: the phase $(-1)^{b \cdot v}$ combines
with $(-1)^{v \cdot w}$. So phase errors move the index $w$, and they leave the code exactly when
$b \notin C_2^{\perp}$. In Calderbank and Shor's words, phase errors in the original basis are bit
errors in the rotated basis, where the codewords are superpositions of $|v\rangle$ with
$v \in C_2^{\perp}$, and they are detected by the classical code $C_2^{\perp}$; correcting a family of
them needs a distance condition on $C_2^{\perp}$, as in
[CSS codes correct $\lfloor (d - 1)/2 \rfloor$ errors](is-correctable-css.md).

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section III, equations (5)–(6) and the discussion after equation (9).
