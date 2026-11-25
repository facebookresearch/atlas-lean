# Formal inverses of restricted power series are restricted

Let `𝓞` be a commutative ring, `p` a natural number, and `φ = (φ_1, ...,
φ_d)` a family of power series in `d` variables over `𝓞` with zero constant
terms and identity linear part. Assume:

- `φ` is restricted: for every `N` and `i`, all but finitely many coefficients of `φ_i` lie in the ideal `(p ^ N)`;
- for every `i`, `j` and every monomial `m` of total degree at least `2`, `m_j` times the coefficient of `m` in `φ_i` lies in `(p)`;
- `ψ = (ψ_1, ..., ψ_d)` is a formal inverse in the sense that substituting `φ` into `ψ_i` gives `X_i` for every `i`;
- there are polynomials `χ_1, ..., χ_d` over `𝓞` with zero constant terms such that, for every `i`, every coefficient of `φ_i(χ) - X_i` lies in `(p)`.

Then `ψ` is restricted: for every `N` and `i`, all but finitely many
coefficients of `ψ_i` lie in `(p ^ N)`.
