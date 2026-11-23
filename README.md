# How Random Automata Forget Their Initial State

Lean proofs accompanying Yilin Cheng's paper. The two modules use only the Lean standard library.

## Reproduce the checks

With elan installed, run the following commands from the repository root. The toolchain file selects Lean 4.34.0.

```sh
lean --version
lake build
```

## Correspondence with the paper

* **First meetings in a logarithmic window.** In [OverlapWords.lean](OverlapWords.lean), `periodic_agrees`, `prefix_periodic`, and `periodic_prefix` show that periodic extension and taking the first g bits are inverse maps between g-bit seeds and blocks whose two length-d substrings at distance g > 0 agree. The paper counts the seeds to obtain a matching probability of 2⁻ᵈ for independent fair input bits, including when the substrings overlap.
* **From first meetings to survival probabilities.** In [SurvivalEnvelope.lean](SurvivalEnvelope.lean), `blockRatios` propagates a lower bound from a delayed loss inequality, and `upperBarrier` compares a delayed upper recurrence with a supersolution. Both statements use rational sequences and take the recurrence inequalities as hypotheses.

The paper proves the random-table estimates that supply these hypotheses and uses them to obtain the synchronization and learning results.
