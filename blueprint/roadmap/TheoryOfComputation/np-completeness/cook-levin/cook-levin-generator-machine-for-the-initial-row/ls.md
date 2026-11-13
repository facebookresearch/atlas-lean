# Stages of the literal routine (initial-row generator)

The stages of the generator's
routine that emits one literal of a clause: two stages copying the clause base into a target
counter, a stage adding the literal's offset to the target, a stage decrementing the position
counter, a stage comparing the position with the target, two restore stages for each comparison
outcome (less, equal or greater), a stage emitting one empty slot, a halting error stage, a stage
emitting the literal's slot, and a stage draining the target counter.
