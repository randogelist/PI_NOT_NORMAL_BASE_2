# Proof frontier

The retained objective is `π is not normal in base 2`, pursued through the frozen real coefficient

\[
C_t=\frac{(-1)^t}{4}.
\]

No recovered branch establishes the missing distribution statement for the actual binary digits of π. The repository is a verification of the recovered analytic, combinatorial, and conditional progress. Its name describes the research target. Historical theorem names containing `A_TIER` or `FULL_CLOSURE` are preserved identifiers, not unconditional proof claims.

## Primary actual-digit route: residual-tail frequencies

Source identity: `PI_DYADIC_CT_v0_7_0`.

Let

\[
b_n=\mathbf 1_{\{\{2^n\pi\}\ge1/2\}},\qquad
S_\pi(m)=\sum_{j<m}(b_{2j}-b_{2j+1}).
\]

The source constructs its actual analytic drift without a caller-supplied positivity hypothesis:

\[
a_j=\begin{cases}0,&j<512,\\D(2j)+D(2j+1),&j\ge512,\end{cases}
\quad A(m)=\sum_{j<m}a_j,\quad E_\pi(m)=S_\pi(m)-A(m),
\quad0\le a_j\le\tfrac12.
\]

For a fixed integer `r ≥ 1`, write `u_r=(01)^r0`, `v_r=(10)^r1`, and

\[
F_M(r)=f_M(u_r)+f_M(v_r),\qquad
T_E(h,N)=\frac1N\#\{j<N:|E_\pi(j)|\ge h\}.
\]

The unconditional finite estimate implemented by `PI_ALTERNATING_FREQUENCY_TAIL_BOUND` is

\[
F_{2N}(r)\le2T_E(r/4,N)+\frac{r+1/2}{N}\qquad(N>0).
\]

An alternating block forces an excursion of the actual residual; this is a finite counting theorem. Its right-hand side is not already controlled asymptotically.

The sufficient open input to `PI_NOT_NORMAL_OF_SMALL_ANALYTIC_RESIDUAL_TAIL` is

\[
\exists r\ge1\;\exists\eta\ge0\;\exists N_0:
\quad2\eta<4^{-r}\quad\land\quad
\forall N\ge N_0,\ T_E(r/4,N)\le\eta.
\]

Normality would force `F_(2N)(r) → 4^(-r)`, contradicting this input and the finite bound. The input has not been proved for π. A finite sample, an analytic coefficient sign, or the fact that longer words are rarer does not establish it. The word length must remain fixed while the sample size tends to infinity.

Other retained sufficient routes include a persistent fixed-length alternating-word deficit, bounded actual analytic/harmonic residual, and bounded pair-walk drawdown or reflected counter. These have different hypotheses. They must not be silently identified or counted as discharged by each other.

## Analytic-observation route

Source identity: `ANCHOPI_PI_NONNORMAL_FULL_CLOSURE_LEAN_v0_8_0_FIX2_FASTSTART`.

The logarithmic kernel is

\[
M(N)=\frac{\log(1+1/N)}{\log(1+2/N)},\qquad
D(N)=\frac{\log(1+1/[N(N+2)])}{2\log(1+2/N)}.
\]

The source contains proof bodies for `M(N)-1/2=D(N)`, positivity for `N>0`, and

\[
0\le\frac14-ND(N)\le\frac1{N+1}.
\]

With `N_a=2^(10+a)`, its physically scaled family is

\[
H_{\rm an}(a,t)=(-1)^t(N_a+t)D(N_a+t).
\]

It has the uniform error bound

\[
|H_{\rm an}(a,t)-C_t|\le\frac1{N_a+1}.
\]

The remaining digit hypothesis asks for a different family `H(a,t)` which is determined by a finite block of the actual π stream at each scale, and which tracks this analytic family uniformly over all offsets. The final theorem is exactly

```text
ActualPiAnalyticTracking → ¬ normal actualPiDigits
```

The source also gives equivalences

```text
ActualPiAnalyticTracking
  ↔ ActualPiCtTracking
  ↔ Nonempty (ActualPiCtBinding actualPiDigits)
  ↔ FiniteParitySeparation actualPiDigits
  ↔ OneScaleCtApproximation actualPiDigits.
```

The semantic content of `FiniteParitySeparation` is that one fixed block width determines start parity at every position. This digit property remains unproved. Defining `H(a,t)=C_t` supplies the desired numerical limit but does not supply finite observability; doing so without the latter proof would assume the missing bridge.

## Exact-obstruction specification

Source identity: `ANCHOPI_CT_EXACT_OBSTRUCTION_LEAN_v0_2_0`.

```text
Ct(w) := ¬ tends_to (frequency actualPiDigits w) (fair_mass w)
CTπ   := ∃ w, Ct(w)
CTπ ↔ ¬ normal actualPiDigits
```

This is a useful exact specification of the target. It does not derive a bad word from the real coefficient `C_t`. Supplying `CTπ` as a premise supplies the target's entire unresolved distribution content. The earlier single-hypothesis package expresses a persistent nonzero defect explicitly; that version is preserved as a separate historical definition.

## Concrete shell-cancellation route

Source identity: `ANCHOPI_FRONTIER_EXPLICIT_LEAN_v0_4_0_FASTSTART`.

The exact identity is `actualShellGap = analyticShellMass + concretePiRemainder`. The analytic target is `log(2)/4`. The archived Lean source leaves three obligations explicit:

| Obligation | Meaning |
| --- | --- |
| `AnalyticShellLimit` | The concrete positive analytic mass tends to `log(2)/4`. |
| `NormalityKillsActualShell` | Normality of the actual π stream forces the aligned shell statistic to tend to zero. |
| `ActualPiNonCancellation` | The concrete actual remainder does not tend to `-log(2)/4`. |

The first two are identified in the archive as pending Lean ports of historical Rocq results. Together they are the premises of the proof identifying the cancellation that normality requires. They do not establish the third obligation. The earlier reconstructed branch bundles the first two in `ActualPiCancellationData`; bundling does not prove them.

## What coefficient accumulation establishes

The frozen signed coefficients cancel in adjacent pairs:

\[
C_t+C_{t+1}=0,\quad
\sum_{t<L}C_t=\frac{1-(-1)^L}{8},\quad
\sum_{t<L}(-1)^t C_t=\frac L4.
\]

The actual unscaled analytic correction retains a denominator. Its fixed-length total is at most `L/(4M)`, which vanishes as `M` grows. The analytic split-product branch likewise obtains the fair fixed-length limit `2^(-L)` and does not identify those products with actual digit counts. These results rule out treating analytic sign accumulation alone as a persistent word-frequency bias.

The moving-offset result must also remain separate from a fixed-offset limit. Neither pointwise convergence in `t` nor a positive drift alone proves the actual residual-tail estimate.

## Paper continuation, outside the formal closure

`PI_CT_SOURCE_RESEARCH_v1.tex` proposes a separate Gregory-series realization of the same coefficient and a BETA9/AZETON rational recurrence approximating the dyadic π orbit with geometric circle error. It then proposes ordinary continuous moment defects or nonvanishing C_t-weighted correlations as distribution targets.

The note distinguishes the contracting shape part of its recurrence from the expanding arithmetic coordinate. Contraction does not prove the integer itinerary has biased frequencies. Its rational identities, analytical recurrence transfer, moment-density argument, and correlation endpoint are paper-level work unless their corresponding proof-assistant modules are independently supplied and compiled. They are not substitutes for any missing actual-digit estimate above.

## Verification meaning

A current successful CI run must identify its commit, toolchain, dependency revision, compiled source set, and axiom-audit result. Only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) may remain in audited target dependencies; no `sorryAx` or project research axioms may be admitted.

Compilation of an implication gives a proof of that implication. It does not prove an explicit input, produce a finite raw-data witness, or turn a historical title into an unconditional theorem. The archived v0_7_0 validation and v0_8_0 partial-pass history remain distinguishable from this repository's current build evidence.
