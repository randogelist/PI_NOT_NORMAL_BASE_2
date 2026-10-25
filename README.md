# Pi non-normality in base 2 — the C_t route

[![Lean C_t verification](https://github.com/randogelist/PI_NOT_NORMAL_BASE_2/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/randogelist/PI_NOT_NORMAL_BASE_2/actions/workflows/lean.yml)

This repository consolidates the recovered ANCHOPI and PI_DYADIC_CT Lean research branches. Its purpose is to verify the progress toward proving that π is not normal in base 2, while preserving the original analytic C_t route and every unresolved hypothesis.

**This repository does not prove that π is non-normal.** The analytic coefficient is proved; a sufficient estimate about the actual binary digits of π remains open. A successful build certifies the precise conditional theorems in the sources.

## Preprint

[Read the preprint (PDF)](paper/pi_ct_preprint.pdf): **The C_t Route toward Binary Non-Normality of Pi: Formalized analytic progress and an explicit residual-tail criterion**. The [editable LaTeX source](paper/pi_ct_preprint.tex), [theorem map](paper/theorem-map.json), and [verified baseline](paper/verification-baseline.json) accompany it.

## Preserved C_t construction

The primary branch is `PI_DYADIC_CT_v0_7_0`, using the representative

\[
P(z)=4\arctan_{\mathbb C}(z),\qquad P(1)=\pi,
\qquad C_t=\operatorname{Pi.C_T}(t)=\frac{(-1)^t}{4}.
\]

The coefficient is extracted from a unique dyadic limit. Its value, nonvanishing, remainder estimate and Cauchy estimate have no caller-supplied analytic premises. The actual digit stream is bound to

\[
b_n=\mathbf1_{\{\{2^n\pi\}\ge1/2\}}.
\]

| Layer | Principal declaration | Meaning |
|---|---|---|
| Actual π anchor | `PiCt.PI_ANCHOR` | The representative evaluates to `Real.pi` |
| Frozen coefficient | `PiCt.PI_CT_VALUE`, `PiCt.PI_CT_NE_ZERO` | Original C_t value and nonvanishing |
| Actual digits | `PiCt.BinaryWords.piBits_eq` | Identification with the canonical binary digits of π |
| Actual finite frequency bound | `PiCt.AlternatingTailClosure.PI_ALTERNATING_FREQUENCY_TAIL_BOUND` | Unconditional estimate in terms of the actual residual tail |
| Conditional endpoint | `PiCt.AlternatingTailClosure.PI_NOT_NORMAL_OF_SMALL_ANALYTIC_RESIDUAL_TAIL` | Non-normality follows if the specified tail estimate is proved |
| Historical exact obstruction | `ANCHOPI.CTClosure.CT_EXACTLY_PI_NOT_NORMAL_BASE2` | Equivalent word-frequency reformulation; no witness is supplied |

The strongest recovered finite estimate controls the sum of the frequencies of the two alternating words of length `2r+1`:

\[
F_{2N}(r)\le 2T_E(r/4,N)+\frac{r+1/2}{N}\quad(N>0),
\]

where `E` is the exact actual-digit residual against the analytic drift. The non-normality endpoint still requires an eventual bound `T_E(r/4,N) ≤ η` for a fixed `r`, with `2η < 4⁻ʳ`. Neither that bound nor a replacement digit-tracking witness is claimed here.

## Source branches and scope

`PiCt/` preserves all 27 modules from the October 23 dyadic branch. `PiCtAudit.lean` preserves its original `Main.lean`. Seven isolated historical projects in `branches/` preserve the earlier coefficient, contradiction, exact cancellation, explicit frontier, analytic closure and word-obstruction developments. Separate search paths prevent colliding module names from silently selecting the wrong branch.

Read [the source audit](docs/SOURCE_AUDIT.md) and [the proof frontier](docs/PROOF_FRONTIER.md). In particular:

- The analytic real-valued `C_t` is distinct from the later proposition `Ct(word)` meaning failure of a fair-frequency limit. The latter equivalence does not prove existence of an obstruction.
- An old Part B address premise is impossible at index zero. Its historical wrapper is retained for audit, not promoted as a viable closure.
- Signed coefficient cancellation, vanishing fixed-word analytic corrections, and the absence of a proved equality between analytic split products and actual digit frequencies remain explicit.

Source archive hashes and exact branch identities are recorded in `provenance/` and each historical branch's `SOURCE_IDENTITY.json`. The 25 supplied ZIPs were also inspected; their π content concerns irrationality calibration, not the recovered normality route.

Integration edits narrow broad Mathlib imports and supply explicit dependencies. The primary branch's theorem statements and proof bodies are unchanged, as checked against the source archive; see `provenance/PRIMARY_SOURCE_MAP.json` and `PRIMARY_IMPORT_ADAPTATION.diff`. `branches/part-b/AuditFindings.lean` is a new proof of the legacy address obstruction, kept separate from the original source.

## Verification — GitHub CI only

The authoritative repository is [randogelist/PI_NOT_NORMAL_BASE_2](https://github.com/randogelist/PI_NOT_NORMAL_BASE_2). **Do not compile Lean locally.** All compilation, proof-checking and axiom auditing for this repository run on its GitHub Actions runner, as instructed by the owner.

Lean is pinned to `leanprover/lean4:v4.33.0`; Mathlib is pinned to commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The workflow installs the official Lean release with a verified archive checksum, fetches compatible Mathlib artifacts, verifies the audit rejection behavior, compiles all eight projects, and audits transitive axiom dependencies for every project declaration. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

Pushes and pull requests trigger `.github/workflows/lean.yml`. It also supports manual **Run workflow** in Actions. The verifier scripts are guarded to run only in this repository's GitHub Actions environment. Compatible project artifacts can be reused only after source, dependency, compiler and output fingerprint checks.

Use the **Lean C_t verification** run for the exact pushed commit as the evidence. Its artifact contains `verification/CI_RUN.json`, `receipt.json`, per-project `axioms.json`, and compiler logs. A configured workflow or a successful push does not mean the hosted proof check passed. Prior local preparation logs are not included as CI evidence.

The original `YOU_ARE_GOODWORKFLOWFRONTIER` v1_0_15 definition is preserved in `provenance/`. The owner's current instruction overrides its old native-Windows runner: verification is CI-only, while the proof-tier thresholds, branch identities and integrity-checked cache reuse are preserved. No Windows `.olean` files are reused as Linux artifacts.
