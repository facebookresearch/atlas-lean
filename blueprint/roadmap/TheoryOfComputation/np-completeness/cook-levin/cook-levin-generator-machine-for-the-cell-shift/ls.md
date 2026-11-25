# Stages of the cell-shift literal routine

The routine emitting one literal has fifteen
stages: two copy stages, an offset stage, a decrement stage, a compare stage, two restore stages
for each comparison outcome (less, equal, greater), an absent-slot emission stage, a failure
stage, a slot emission stage and a drain stage.
