# GitHub runner

The owner selected `randogelist/PI_NOT_NORMAL_BASE_2` and explicitly requires CI-only Lean verification. Do not run Lean or Lake locally.

The `Lean C_t verification` workflow runs on each push and pull request and supports manual dispatch in Actions. It installs pinned Lean 4.33.0 and pinned cached Mathlib, compiles the primary and seven historical projects in isolated search paths, and audits every declaration. No hosted PASS is inferred from source preparation or earlier local logs.

The workflow uploads commit-specific receipts and logs even on failure. The initial runner step clears earlier checked-in verification output; `CI_RUN.json` identifies the current commit and workflow run. Every proof result must be tied to that run and commit.

Subsequent fixes must be source-only local edits followed by a push and CI inspection. Preserve the C_t route and all explicit open digit-distribution hypotheses.
