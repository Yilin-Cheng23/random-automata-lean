# Polynomial-Time Learning of Random Automata from One Label per Word

[Paper (arXiv:2611.32959v1)](https://arxiv.org/abs/2611.32959v1) · [Lean source snapshot cited in v1](https://github.com/Yilin-Cheng23/random-automata-lean/tree/aa71e6964fbe26627926770155acf7244a7b8d51)

This Lean project accompanies Yilin Cheng’s paper on learning a random binary deterministic finite automaton from uniformly sampled words and their final acceptance bits. It contains 22 modules checking selected steps of the proofs. The paper gives the probabilistic estimates for a shared random transition table and the proof of the learning guarantee.

## Reproduce the checks

From the repository root, with elan and Bash installed, run

```sh
lake exe cache get
bash verify.sh
```

The project pins Lean 4.34.0 in `lean-toolchain` and the Mathlib revision in `lake-manifest.json`. The script compiles all 22 modules in dependency order with warnings treated as errors, then runs `leanchecker --fresh` on each module.

## Where to start

* [OverlapWords.lean](OverlapWords.lean) formalizes the bijection for matching overlapping substrings. [SurvivalEnvelope.lean](SurvivalEnvelope.lean) checks the deterministic recurrence comparisons used in the meeting-time proof.
* [FourSourceCoefficient.lean](FourSourceCoefficient.lean) evaluates the finite sum for two ordered joins in the four-trajectory calculation.
* [AdjacentHistory.lean](AdjacentHistory.lean) checks identities used to recover a moment from adjacent history lengths.
* [DeletionRootGap.lean](DeletionRootGap.lean) checks the deterministic counting and balance steps used to bound the spectral-root gap after deleting states.

The [verification script](verify.sh) lists every module.
