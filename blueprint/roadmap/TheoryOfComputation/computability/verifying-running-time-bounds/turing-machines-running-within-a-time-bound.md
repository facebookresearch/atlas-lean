# Turing machines running within a time bound

A deterministic Turing machine runs in time $T(n)$ if on every input of length $n$ it makes at most $T(n)$ steps. The
verification problems ask, for a given machine, whether it runs in time $T(n)$, or in time bounded by some function of a
class.

**Machines.** Machines are deterministic. A *multi-tape* Turing machine has a read-only input tape and finitely many work
tapes, all of them both-way infinite, with states including an accepting and a rejecting halting state. A *one-tape* Turing machine has a single both-way
infinite read-write tape that also contains the input, and its head moves left or right at every step. On an input $w$ a
machine either halts (accepting or rejecting) or runs forever; every machine makes at least one step on every input.

**Time bounds.** Let $\mathbb{R}_{\ge 0}$ be the set of nonnegative reals and $T : \mathbb{N} \to \mathbb{R}_{\ge 0}$ any
function. A machine $M$ *runs in time $T(n)$* if for every $n \in \mathbb{N}$ it makes at most $T(n)$ steps on every input of
length $n$; in particular it halts on all inputs. No computability or monotonicity of $T$ is assumed.

**Verification problems.** Machines are given by a canonical encoding, and a problem is *decidable* if some multi-tape
Turing machine halts on every encoding and accepts exactly the encodings of its yes-instances.

- $\mathrm{HALT}_{T(n)}$: the set of multi-tape Turing machines that run in time $T(n)$;
- $\mathrm{HALT}^1_{T(n)}$: the set of one-tape Turing machines that run in time $T(n)$;
- for a class $\mathcal{F}$ of functions $\mathbb{N} \to \mathbb{R}_{\ge 0}$, $\mathrm{HALT}_{\mathcal{F}}$ (resp.
  $\mathrm{HALT}^1_{\mathcal{F}}$): the set of multi-tape (resp. one-tape) Turing machines that run in time $T(n)$ for some
  $T \in \mathcal{F}$.

Here $\mathsf{P}$ denotes the class of polynomial functions and $\mathsf{EXP}$ the class of exponential functions $\mathbb{N} \to \mathbb{R}_{\ge 0}$, as classes of time bounds, not of languages; and for $T : \mathbb{N} \to \mathbb{R}_{\ge 0}$, $O(T(n))$ is the class of $f : \mathbb{N} \to \mathbb{R}_{\ge 0}$ with $f(n) \le c\,T(n)$ for some $c$ and all large enough $n$. So $\mathrm{HALT}_{O(1)}$ is the set of multi-tape machines running in constant time, and $\mathrm{HALT}_{\mathsf{P}}$ the set of those running in polynomial time.


If $T(n_0) < n_0 + 1$ for some $n_0$, a machine running in time $T(n)$ never reads past the first $n_0$ input symbols, so it
runs in constant time; this is why the threshold $T(n) \ge n + 1$ appears in the results of this folder.

## Depends on

- [Time-bounded multi-tape machine](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/time-bounded-by.md)
- [Decidability by multi-stack machines](../decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Sources

- D. Gajser, "Verifying time complexity of Turing machines", *Theoretical Computer Science* 600:86–97, 2015, doi:[10.1016/j.tcs.2015.07.028](https://doi.org/10.1016/j.tcs.2015.07.028). Numbering of the version read, arXiv:1307.3648v2 (titled "Verifying Time Complexity of Deterministic Turing Machines"): Section 2 (the models, the definition of running in time $T(n)$ and the decidability conventions) and Section 1 (the problems $\mathrm{HALT}_{T(n)}$ and $\mathrm{HALT}^1_{T(n)}$).
