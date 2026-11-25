# SSR-safe locking policies

A locking policy is SSR-safe when, for every list of pairwise distinct transactions obeying the model assumptions and every choice of locked versions from the policy, every legal schedule of them without the locks is state serializable.
