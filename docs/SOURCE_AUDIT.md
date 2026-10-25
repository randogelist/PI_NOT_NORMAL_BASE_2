# Source audit

Integration note: broad Mathlib imports are narrowed where needed for predictable memory use. Original and current source hashes are retained. The primary statement/proof bodies were compared against the archive after removing import lines and are identical. A new separate `AuditFindings.lean` records the old Part B address obstruction; it does not alter the historical theorem.

The repository preserves the analytic `C_t` route and its actual-digit conditional endpoints. No recovered source proves the remaining actual-π distribution premise. A successful build verifies the exact theorem statements, including their hypotheses; it does not remove those hypotheses.

This source review is dated 2026-10-25. Archived validation statements below are historical evidence. Current verification must be read from the CI run for the corresponding commit and its axiom-audit artifact.

## Recovered branch identities

| Exact branch/package identity | Content retained or considered | Evidence and boundary |
| --- | --- | --- |
| `PI_DYADIC_CT_v0_7_0` | Frozen `Pi.C_T`, logarithmic representative, actual bits, moving-offset profiles, analytic drift, drawdown/counter interfaces, alternating-word frequency and residual-tail closures | `VALIDATION_SCOPE.txt` records five new modules plus updated Main compiled under Lean 4.33.0, 56 public theorem audits, and 22 unchanged earlier modules. These are archived reports, not the current CI result. The actual residual-tail estimate remains unproved. |
| `ANCHOPI_PI_NONNORMAL_FULL_CLOSURE_LEAN_v0_8_0_FIX2_FASTSTART` | 14-module analytic coefficient derivation, uniform physical-scaling limit, exact floor-defined π stream, finite-observation contradiction, frontier equivalences | Source status says FIX2 was not compiled; FIX1 had ten user-reported passed modules before a `CtAnalyticLimit` failure. The repaired source must be compiled afresh. `ACTUAL_PI_FULL_A_TIER_CLOSURE` still assumes `ActualPiAnalyticTracking`. |
| `ANCHOPI_CT_EXACT_OBSTRUCTION_LEAN_v0_2_0` | `CTπ ↔ ¬ normal actualPiDigits` | This is an exact logical reformulation using a fixed-word failure predicate. It neither constructs a witness nor identifies that predicate with the analytic coefficient. |
| `ANCHOPI_CT_SINGLE_HYPOTHESIS_LEAN_v0_1_2_FIX2` | A fixed word with a persistent positive frequency defect implies nonnormality | The persistent defect remains the sole research premise. Its `Ct` identifier is a proposition, not a real coefficient. |
| `ANCHOPI_PART_A_CT_LEAN_v0_1_5_FIX4_FASTSTART` | π/4 integral anchor, integer-feedback radix readout, positive logarithmic defect, signed shell-scaled coefficients | Its `STATUS.txt` still names v0_1_2 FIX1 and is stale relative to the archive identity. A later Part-B status reports Part A passed. Use source hashes and current compilation, not the stale version line, for verification. |
| `ANCHOPI_PART_B_CT_CONTRADICTION_LEAN_v0_2_1_FIX1` | Generic bounded-remainder forbidden-word argument | The generic `CtDriftBridge` result is meaningful. The specialized `CtDigitBridge` has an impossible all-index address field; see below. Its normality wrapper also takes an abstract normality-to-recurrence implication. |
| `ANCHOPI_RECONSTRUCTED_CHAIN_LEAN_v0_3_1_FIX1_FASTSTART` | Historical vanishing-coefficient/bounded-remainder anchor and exact cancellation interface | `ActualPiCancellationData` carries both analytic shell convergence and normality-to-shell convergence as proof fields. The structure is an interface, not a constructed actual-π instance. |
| `ANCHOPI_FRONTIER_EXPLICIT_LEAN_v0_4_0_FASTSTART` | Concrete actual shell statistic, concrete analytic shell mass, exact remainder | `AnalyticShellLimit`, `NormalityKillsActualShell`, and `ActualPiNonCancellation` remain explicit. Its status calls the first two open Lean ports from Rocq. |
| `PI_CT_SOURCE_RESEARCH_v1.tex` | 2026-10-23 paper continuation: Gregory realization, BETA9/AZETON rational orbit, continuous moment and C_t-correlation tests | The note explicitly says no new Lean/Rocq build was run and no persistent defect was established. Its new paper results are not counted as kernel-verified repository progress. |

The 25 initially attached ZIPs were separately examined, including the nested witness archive. They supplied zeta work and π irrationality calibration, but not the requested C_t normality route. In particular, `CLASSIFIER_64_PI_BKQR_CALIBRATION_v0_5_2_FIX2` and `GP_NATIVE_E_PI_v0_4_0` are related π arithmetic sources, not nonnormality proofs. The route above came from the subsequently recovered C_t packages.

## Three different uses of “Ct”

1. The old analytic family is
   `ANCHOPI.PartA.Ct a t = (-1)^t N_a D(N_a+t)`, with `N_a = 2^(10+a)`.
2. The frozen limiting real coefficient is
   `Pi.C_T t = ANCHOPI.PartA.limitingCt t = (-1)^t / 4` mathematically. Separate namespaces do not themselves provide a compiled cross-project equality.
3. `ANCHOPI.CTClosure.Ct w` is a proposition indexed by a finite Boolean word. In v0_2_0 it is the negation of fair-frequency convergence. In v0_1_2 it is a persistent positive frequency defect.

The exact-obstruction branch contains a proof of the equivalence between item 3's existential witness and nonnormality. It does not prove that item 2 supplies that witness. The two versions of `Closure/ConditionalCT.lean` also reuse declaration names for different definitions and must not overwrite one another in a single build tree.

## Mathematical issues found

### An impossible legacy coordinate interface

In Part B v0_2_1, `CtDigitBridge.address` requires

```text
∀ j, 2*j = shellN (a j) + t j
```

with `shellN (a j) = 2^(10+a j) > 0`. At `j=0`, this asserts zero equals a positive natural number plus another natural number. Consequently no `CtDigitBridge` can exist, for any bitstream. Its specialized conditional endpoint is vacuous. The repository adds `branches/part-b/AuditFindings.lean`, theorem `ctDigitBridge_impossible`, to make this finding checkable by Lean; consult the current branch audit result before treating that new declaration as verified.

This does not invalidate the separate generic bounded-remainder proof. The later `DyadicPairCoordinates` interface in `AWPI/VanishingCoefficientsAnchor.lean` restricts its address obligation to `j ≥ J`, which removes the zero-index obstruction. A repaired legacy interface must use an explicit cutoff and be named/versioned as a repair; the historical source should remain identifiable.

### Shell scaling and physical scaling are different

For `D(N) = log(1+1/[N(N+2)]) / (2 log(1+2/N))`, fixed-offset convergence of `N_a D(N_a+t)` to `1/4` does not give uniform convergence over all offsets. At moving offsets comparable to `N_a`, the profile changes; the old diagonal `t=N_a-1` approaches `1/8`. The physical scaling `(N_a+t) D(N_a+t)` is the one used by v0_8_0 for uniform convergence to `1/4`.

No shell-only pointwise limit is substituted for the uniform hypothesis in the finite-observation closure. The v0_8_0 source's `ANALYTIC_BINDING_FINDINGS.txt` also gives a paper argument that the raw analytic array cannot itself be a finite-window observable of any bitstream. That obstruction is source-derived mathematics, not a separately compiled theorem here.

### Finite observation is a strong digit condition

The v0_8_0 tracking premise is equivalent to one finite word width that distinguishes every even start from every odd start. The equivalence is formalized in `FiniteParityFrontier`. It is strictly stronger than arbitrary nonnormality: a constant bitstream is nonnormal but cannot decode start parity from any fixed window. Thus this premise must not be advertised as an already automatic analytic-to-digit identification.

### Index conventions

The modern `ActualPi/PiReadout.lean` uses digit zero as the first fractional bit: parity of `floor(2^(n+1) π)`. Old radix modules use exponent `n`; some historical streams add a dummy zero at index zero. The reconstructed cancellation branch instead evaluates the exponent-zero parity directly. These are distinct prefix/index conventions. A one-place shift reverses an alternating sign, so any pointwise bridge must state its shift and phase explicitly. Normality's prefix invariance alone does not identify the formulas.

### A record is not a finite accepted witness

`ActualPiCtBinding` and `PiCtWitness` contain infinite functions and proof fields. `ActualPiCancellationData` contains analytical convergence proofs. Their use in conditional theorems is legitimate, but their mere declaration is neither raw finite witness admission nor evidence that an actual-π instance exists.

## Build selection

The primary `PiCt` project should retain all modules from `PI_DYADIC_CT_v0_7_0`, because it contains the most developed recovered actual-digit finite-frequency bounds. The analytic-observation v0_8_0 branch supplies a distinct, valuable closure and should be compiled as its own project. The exact-obstruction v0_2_0 branch supplies a small logical target specification and should be kept separately identified.

For comprehensive historical replay, compile Part A, Part B, reconstructed cancellation, concrete frontier, and the single-hypothesis branch in isolated subprojects. They reuse `PartA`, `PartB`, `Closure`, `Main`, and theorem namespaces with differing contents. Do not put every archive on one Lean search path. Isolated source roots and build output directories prevent one branch's `.olean` from satisfying another branch's import accidentally.

The preserved `.v` files in the full closure package are historical Rocq evidence excerpts, not a Rocq build. Their `SOURCE_MAP.txt` traces them to `awpi_master_discussion_2026-09-06/00_original_uploads/NormalityClosure(2).zip`. Current Lean CI does not certify those Rocq sources.
