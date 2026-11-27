# Integral representation of relative entropy by the resolvent kernel

Let $\rho,\sigma$ be positive semidefinite with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. The function $s \mapsto \big(R_{s/(1-s)}(\rho,\sigma) - (1-s)\operatorname{Tr}\rho\big)/(1-s)^2$ is integrable on $[0,1]$ and

$$
D(\rho\,\|\,\sigma) = \int_0^1 \frac{R_{s/(1-s)}(\rho,\sigma) - (1-s)\operatorname{Tr}\rho}{(1-s)^2}\,ds .
$$

## Proof sketch

By the spectral formula for $R_t$ the integrand is a nonnegative combination, with weights $|\langle u_j,v_i\rangle|^2$, of the scalar integrands $\lambda(\lambda-\mu)/((1-s)\mu + s\lambda)$. Each integrates over $[0,1]$ to $\lambda\log(\lambda/\mu)$, and summing recovers $\operatorname{Tr}\rho\log\rho - \operatorname{Tr}\rho\log\sigma$; support inclusion ensures every term with $\mu = 0$ has $\lambda$-weight zero.

## Depends on

- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)
- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)

## Proof depends on

- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)

## Sources

- M. B. Ruskai, "Another short and elementary proof of strong subadditivity of quantum entropy", Reports on Mathematical Physics 60(1):1-12, 2007.
