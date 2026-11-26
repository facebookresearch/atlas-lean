# Regret bound for the matrix multiplicative weights update

Let $M^{(1)}, \dots, M^{(T)}$ be Hermitian $D \times D$ matrices with $0 \preceq M^{(t)} \preceq I$, let $\eta > 0$, and define density matrices

$$
\rho^{(t)} = \frac{\exp\big(-\eta \sum_{s < t} M^{(s)}\big)}{\mathrm{Tr} \exp\big(-\eta \sum_{s < t} M^{(s)}\big)} .
$$

Then for every density matrix $\sigma$,

$$
\bigl(1 - e^{-\eta}\bigr) \sum_{t=1}^T \langle M^{(t)}, \rho^{(t)} \rangle \le \eta \sum_{t=1}^T \langle M^{(t)}, \sigma \rangle + \ln D .
$$

## Proof sketch

Track the potential $\Phi_t = \mathrm{Tr} \exp(-\eta \sum_{s<t} M^{(s)})$. The Golden-Thompson inequality gives $\Phi_{t+1} \le \mathrm{Tr}[\exp(-\eta \sum_{s<t} M^{(s)}) \exp(-\eta M^{(t)})]$, and $\exp(-\eta M) \preceq I - (1 - e^{-\eta}) M$ for $0 \preceq M \preceq I$, so $\Phi_{t+1} \le \Phi_t (1 - (1 - e^{-\eta}) \langle M^{(t)}, \rho^{(t)}\rangle)$. Comparing $\ln \Phi_{T+1}$ from above with the lower bound $\Phi_{T+1} \ge \exp(-\eta \sum_t \langle M^{(t)}, \sigma \rangle)$, which follows from the Peierls-Bogoliubov (Gibbs variational) inequality, and using $\Phi_1 = D$ and $\ln(1-u) \le -u$, yields the bound. The form $(1+\eta)\sum_t\langle M^{(t)},\sigma\rangle + (\ln D)/\eta$ is false for this update: with $D=2$, ten losses $M^{(t)}=\mathrm{diag}(0,1)$, $\sigma=\mathrm{diag}(1,0)$ and $\eta=1/2$, the learner's loss is $1.6297\ldots$, while that bound is $2\ln 2 = 1.3863\ldots$.

## Sources

- Sanjeev Arora, Satyen Kale, "A combinatorial, primal-dual approach to semidefinite programs", STOC (2007); Journal of the ACM 63(2) (2016) (matrix multiplicative weights potential argument).
- Rahul Jain, Zhengfeng Ji, Sarvagya Upadhyay, John Watrous, "QIP = PSPACE", Journal of the ACM 58(6) (2011), STOC (2010); arXiv:0907.4737.
