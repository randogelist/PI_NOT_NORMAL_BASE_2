# Working on this repository

Preserve the C_t analytic route, exact branch identities and explicit open hypotheses. Never report an unconditional π non-normality proof from a conditional theorem, reformulation, finite numerical check, or successful build alone.

DO NOT execute Lean or Lake locally. Compilation and audits must run exclusively on GitHub Actions in randogelist/PI_NOT_NORMAL_BASE_2. Local source edits and non-Lean static inspection are allowed. Use the pinned Lean and Mathlib versions on the CI runner. Keep historical branches in isolated search paths. Do not add `sorry`, `admit`, project axioms or unchecked proof shortcuts. Push the changes to the authorized repository and inspect its commit-specific CI verifier and transitive axiom audit. Reuse compiled modules only when their source, dependency, toolchain and artifact fingerprints match.

Record any change to recovered sources against their original hashes. Keep local compilation, historical user reports and GitHub Actions results distinct. Follow the user's current instruction when it overrides the historical workflow definition.
