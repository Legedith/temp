# Lonely Runner: finite correlated-amplitude core in Lean 4

This branch formalizes the finite algebraic and graph-theoretic core of a proposed
correlated-amplitude Riesz-product method for the Lonely Runner Conjecture.

Machine-checked target scope:

* uniform finite averages;
* a pair-cancelling amplitude-law interface;
* transfer of cancellation through a proper graph coloring;
* vanishing of arbitrary weighted quadratic edge sums;
* the square-root obstruction for any law cancelling every distinct pair;
* the affine centered-sign calculation that produces exact pair cancellation.

Not claimed by this project:

* a proof of the Lonely Runner Conjecture;
* a formal proof of the Bonami--Rudin progression estimate;
* a formal proof of the full asymptotic chromatic Riesz estimate.

The checked source contains no `sorry` declarations and no axioms. CI invokes
Lean's independent `leanchecker` after `lake build`.
