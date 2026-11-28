# Integral representation of relative entropy by the resolvent kernel

Let $\rho,\sigma$ be positive semidefinite with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. The function $t \mapsto R_t(\rho,\sigma) - \operatorname{Tr}\rho/(1+t)$ is integrable on $(0,\infty)$ and

$$
D(\rho\,\|\,\sigma) = \int_0^\infty \Big( R_t(\rho,\sigma) - \frac{\operatorname{Tr}\rho}{1+t} \Big)\,dt .
$$

Equivalently, substituting $t = s/(1-s)$, the function $s \mapsto \big(R_{s/(1-s)}(\rho,\sigma) - (1-s)\operatorname{Tr}\rho\big)/(1-s)^2$ is integrable on $[0,1]$ and

$$
D(\rho\,\|\,\sigma) = \int_0^1 \frac{R_{s/(1-s)}(\rho,\sigma) - (1-s)\operatorname{Tr}\rho}{(1-s)^2}\,ds .
$$

## Proof sketch

Write $\Delta = L_\sigma R_\rho^{-1}$ (left multiplication by $\sigma$ and right multiplication by $\rho^{-1}$, which commute). Ruskai writes the relative entropy as $D(\rho\|\sigma) = -\operatorname{Tr}\big((\log\Delta)(\rho)\big)$ and substitutes $w = \Delta$ in the scalar identity $-\log w = \int_0^\infty \big(\frac{1}{w+t} - \frac{1}{1+t}\big)\,dt$, giving $D(\rho\|\sigma) = \int_0^\infty \big(\operatorname{Tr}\big((\Delta + t)^{-1}(\rho)\big) - \operatorname{Tr}\rho/(1+t)\big)\,dt$, with no trace condition. Since $(\Delta + t)^{-1} = R_\rho (L_\sigma + tR_\rho)^{-1}$ and $\operatorname{Tr}R_\rho(Y) = \operatorname{Tr}\rho Y$, the trace is $\operatorname{Tr}\,\rho\,(L_\sigma+tR_\rho)^{-1}(\rho) = R_t(\rho,\sigma)$.

For singular $\rho$ or $\sigma$ use the spectral formula for $R_t$: the pair $(j,i)$ contributes $|\langle u_j,v_i\rangle|^2\lambda_j\big(\frac{1}{\mu_i/\lambda_j + t} - \frac{1}{1+t}\big)$ when $\lambda_j > 0$ and nothing otherwise, and support inclusion gives $\mu_i > 0$ whenever $\lambda_j|\langle u_j,v_i\rangle|^2 > 0$. The scalar identity with $w = \mu_i/\lambda_j$ integrates each contribution to $|\langle u_j,v_i\rangle|^2\lambda_j\log(\lambda_j/\mu_i)$, and the sum is $\operatorname{Tr}\rho\log\rho - \operatorname{Tr}\rho\log\sigma$. The substitution $t = s/(1-s)$, $dt = ds/(1-s)^2$, $1/(1+t) = 1-s$ gives the second form.

## Depends on

- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)
- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)

## Sources

- M. B. Ruskai, "Another short and elementary proof of strong subadditivity of quantum entropy", Reports on Mathematical Physics 60(1):1-12, 2007, Section 2.3, eqs. (8), (11) and (12), with eq. (3) for the definition.
