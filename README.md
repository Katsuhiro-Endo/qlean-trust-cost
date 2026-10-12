# A Concrete Development Example for “Reducing Trust Cost in Quantum Application Development Using AI”

Paper: Katsuhiro Endo, *Reducing Trust Cost in Quantum Application Development Using AI*.

## Checkpoints

| Checkpoint | Mathematical target | Circuit guarantee | Mathematical specification | Circuit definition | Correspondence theorem |
|---|---|---|---|---|---|
| CP01 | Delimiter-encoded generator matrix | Block encoding of the scaled generator | [generatorMatrix](mathematical-specifications/src/QLean/MathematicalSpecifications/Targets.lean#L22) | [generatorCircuit](circuits/src/QLean/Circuits/CheckpointCircuits.lean#L12) | [generatorCircuit_correct](correspondence/src/QLean/Proofs/GeneralScientificPublicCheckpoints.lean#L25) |
| CP02 | History linear-system matrix | Block encoding of the scaled history matrix | [historyMatrix](mathematical-specifications/src/QLean/MathematicalSpecifications/Targets.lean#L35) | [historyCircuit](circuits/src/QLean/Circuits/CheckpointCircuits.lean#L18) | [historyCircuit_correct](correspondence/src/QLean/Proofs/GeneralScientificPublicCheckpoints.lean#L45) |
| CP03 | Kernel-reflection operator | Approximation within the requested error | [kernelReflectionMatrix](mathematical-specifications/src/QLean/MathematicalSpecifications/Targets.lean#L46) | [kernelReflectionCircuit](circuits/src/QLean/Circuits/CheckpointCircuits.lean#L23) | [kernelReflectionCircuit_correct](correspondence/src/QLean/Proofs/GeneralScientificPublicCheckpoints.lean#L58) |
| CP04 | Successful history state | Approximation of the projected output state | [successfulHistoryState](mathematical-specifications/src/QLean/MathematicalSpecifications/Targets.lean#L73) | [successfulHistoryCircuit](circuits/src/QLean/Circuits/CheckpointCircuits.lean#L31) | [successfulHistoryCircuit_correct](correspondence/src/QLean/Proofs/GeneralScientificPublicCheckpoints.lean#L74) |

## Reproduction

Requirements: Lean through elan, Git, Python 3, and the pinned mathlib dependencies. The toolchain is specified in `lean-toolchain`; mathlib is pinned by commit in `lakefile.toml`.

From the repository root on Linux:

```sh
lake update
lake exe cache get
lake build QLeanMathematicalSpecifications
lake build QLeanCircuits
lake build
python3 scripts/resources.py
```

The first target builds `mathematical-specifications` and its common dependencies. The second builds `circuits` and its common dependencies. The default build also includes `correspondence`. They share one Lake package to avoid collisions between module search paths while retaining separate source layers and build targets.

Additional isolated checks are available through `python3 scripts/verify.py math` and `python3 scripts/verify.py circuits`. These select only the requested layer and the common layer, reject forbidden cross-layer imports, and use a separate project module output tree for each target.

Lake outputs are written below `.lake/`. The isolated checks write logs and checked module fingerprints below `build/`. Resource results are written to `build/resource-counts.txt`.

The resource evaluator uses the deterministic upper-left/upper-right input defined in [examples/PaperResources.lean](examples/PaperResources.lean). It evaluates a count formula proved equal to the circuit size, without constructing a list containing all kernel-reflection gates. The formula uses the shape of the proof-chosen QSP word and does not synthesize its real phase values.

External numerical phase words use the same finite circuit constructor. Their approximation accuracy is outside the correspondence theorem for the proof-chosen provider.
