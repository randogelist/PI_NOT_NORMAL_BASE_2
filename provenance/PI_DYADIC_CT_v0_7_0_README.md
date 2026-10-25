# PI_DYADIC_CT_v0_7_0

Long alternating words, actual residual-tail frequencies, and the limit of
what the frozen analytic coefficient mass can establish by itself.

## New exact frequency estimate

The actual bits remain

\[
b_n=\mathbf1_{\{\{2^n\pi\}\ge1/2\}},\qquad
S_\pi(m)=\sum_{j<m}(b_{2j}-b_{2j+1}).
\]

Use the already established exact analytic drift

\[
a_j=\begin{cases}0,&j<512,\\
\delta(2j)+\delta(2j+1),&j\ge512,\end{cases}
\qquad A(m)=\sum_{j<m}a_j,\qquad E_\pi(m)=S_\pi(m)-A(m).
\]

The new source proves `0 <= a_j <= 1/2` without a caller-supplied analytic
hypothesis. It retains the stronger earlier analytic/harmonic error bound.

For a fixed `r >= 1`, consider the two words of length `2*r+1`:

\[
u_r=(01)^r0,\qquad v_r=(10)^r1.
\]

Let `f_M(w)` count occurrences among the first `M` starting positions and
divide by `M`. Words starting near the end may extend beyond those positions.
Define

\[
F_M(r)=f_M(u_r)+f_M(v_r),\qquad
T_E(h,N)=\frac1N\#\{j<N:|E_\pi(j)|\ge h\}.
\]

For every `N > 0`, Lean checks the unconditional actual-pi estimate

\[
\boxed{F_{2N}(r)\le 2T_E(r/4,N)+\frac{r+1/2}{N}.}
\]

This follows from exact digit counting:

1. An even-aligned `(01)^r` changes `S` by `-r`; `(10)^r` changes it by `r`.
2. The drift increases by a quantity in `[0,r/2]`. Either kind of block
   therefore forces `|E(j+r)-E(j)| >= r/2`.
3. At least one endpoint satisfies `|E| >= r/4`.
4. Sum endpoint indicators and account for shifted boundaries. Even and odd
   word starts together produce the displayed `(r+1/2)/N` correction.

No independence, stochastic model, digit-frequency bridge, or actual-pi
remainder estimate is assumed in this finite inequality. Its right-hand
side contains the still unevaluated tail frequency of the actual residual.

## Conditional closure through frequencies

Binary normality requires

\[
\forall r\ge1:\quad F_{2N}(r)\longrightarrow4^{-r}.
\]

Thus the following is sufficient:

\[
\boxed{\exists r\ge1\;\exists\eta\ge0\;\exists N_0:\quad
2\eta<4^{-r}\quad\land\quad
\forall N\ge N_0:\ T_E(r/4,N)\le\eta.}
\]

`PI_NOT_NORMAL_OF_SMALL_ANALYTIC_RESIDUAL_TAIL` proves the resulting
nonnormality implication. **It does not establish this tail estimate.**
The condition allows unbounded residuals with sufficiently rare large
excursions. It is sufficient, not necessary.

A uniform bound on the prescribed residual implies this condition by choosing
`r` so large that `r/4` exceeds the bound. The new condition is not asserted
to be equivalent to, or always weaker than, boundedness of the v0.6.0 reflected
counter. Those remain distinct sufficient routes.

`AlternatingFrequency` also supplies a direct deficit criterion for any fixed
positive length `L`:

\[
D_N(L)=1-\frac{2^L}{2}\left[f_N(0101\ldots)+f_N(1010\ldots)\right].
\]

An `epsilon > 0` deficit persisting at arbitrarily large sample sizes
contradicts normality. Both ordinary and dyadic sample-size endpoints retain
that deficit as an explicit hypothesis. **The length is fixed before the
sample size tends to infinity.**

## What accumulating the frozen coefficients actually gives

The frozen object is unchanged:

\[
P(z)=4\arctan_{\mathbb C}z,\quad P(1)=\pi,\qquad
\operatorname{Pi.C_T}(t)=C_t=\frac{(-1)^t}{4}.
\]

The coefficient is still extracted from a proved unique limit. No existence
or analytic premise is supplied by callers of the frozen coefficient API.

New checked summation identities distinguish signed from aligned mass:

\[
C_t+C_{t+1}=0,\qquad
\sum_{t<L}C_t=\frac{1-(-1)^L}{8},\qquad
\sum_{t<L}(-1)^tC_t=\frac L4.
\]

The actual unscaled analytic correction still has a denominator. For `M>0`,

\[
0\le\sum_{t<L}\delta(M+t)\le\frac{L}{4M}.
\]

At the dyadic scale `M=2^(10+a)`, this tends to zero for **every fixed** `L`.
A growing word length and a fixed-word asymptotic are different limits.
The fact that longer words are rarer is compatible with normality; their
normal frequencies themselves decrease exponentially.

## Analytic split products are not identified with digit counts

For an arbitrary fixed sign pattern, the source separately studies

\[
P_{n,L}=\prod_{k<L}\left(\tfrac12\pm\delta(n+k+1)\right).
\]

These are analytic products, with no asserted equality to pi word frequencies.
Lean proves

\[
|P_{n,L}-2^{-L}|\le\frac{L}{4(n+1)},\qquad
P_{n,L}\longrightarrow2^{-L}\quad(L\text{ fixed}).
\]

Their Cesaro averages have the same fixed-length limit. Even choosing a
negative correction in every factor gives only a finite suppression whose
asymptotic deficit vanishes. For the coherent plus and minus products,

\[
P_{n,L}^{+}\ge P_{n,L}^{-},\qquad
P_{n,L}^{+}+P_{n,L}^{-}\ge2\cdot2^{-L}.
\]

This rules out treating accumulation of these small split corrections alone
as a proof of persistent suppression. The new actual-digit frequency route
requires the separate empirical residual-tail estimate above.

## Retained results

All 22 `PiCt` source modules from v0.6.0 are retained unchanged. They include:

- The concrete pi representative, unique internal `Pi.C_T` instance, frozen
  value, dyadic Cauchy bound, and second-order remainder.
- Exact actual bits, word-frequency identities, and the conditional
  `0000`/`1111` route.
- Zero-allowed nonnegative drift closure and even-aligned alternating words.
- The uniform `1/2048` analytic-to-harmonic error and moving-offset profile.
- Exact floor formulas, bounded drawdown equivalences, reflected pair counter,
  and the conditional counter barrier.
- The exact base-four orbit and the obstruction to a universal potential
  inequality at the fixed phase `1/3`.

The four-bit frequency bridge and all actual-pi boundedness hypotheses remain
unproved. The new module does not silently replace or discharge them.

## Source modules added in this version

| Module | Result |
|---|---|
| `AlternatingFrequency` | Actual long-word frequencies, normal targets, and conditional persistent-deficit closures |
| `CoefficientAccumulation` | Signed cancellation, aligned mass, and vanishing fixed-length analytic block mass |
| `AnalyticWordProduct` | Quantitative analytic product bounds, fixed-length limits, and complementary-product mass |
| `AlternatingExcursions` | Alternating blocks force residual excursions; aligned frequency controlled by residual tails |
| `AlternatingTailClosure` | Ordinary overlapping long-word frequency bound and actual-pi conditional tail closure |

## Validation and native Windows replay

The user's native Windows log reported v0.6.0 `BUILD=PASS`. The new source
modules and updated `Main.lean` are checked locally with Lean 4.33.0 on Linux,
with warnings treated as errors. `VALIDATION_SCOPE.txt` records precisely
which checks completed. The printed axiom audit and source hashes are included.
A Linux check is not a claimed native Windows replay.

The native Windows `run.cmd` checks all 28 source files in dependency order.
It uses the same preinstalled Lean 4.33.0 and mathlib cache as previous packages.
No network, Lake, Python, PowerShell, or WSL is invoked by that runner.
Environment overrides `LEAN_EXE`, `CACHE_ROOT`, `MATHLIB_ROOT`, and
`LEAN_JOBS` remain supported. The default mathlib cache is under
`%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1`.

```cmd
cd /d "%USERPROFILE%\Downloads" && tar -xf "PI_DYADIC_CT_v0_7_0.zip" && call "PI_DYADIC_CT_v0_7_0\run.cmd"
```

Final unresolved statuses include:

```
ACTUAL_PI_RESIDUAL_TAIL_ESTIMATE=NOT_PROVED
ACTUAL_PI_ALTERNATING_FREQUENCY_SUPPRESSION=NOT_PROVED
ACTUAL_PI_ANALYTIC_REMAINDER_BOUND=NOT_PROVED
ACTUAL_PI_COUNTER_BOUND=NOT_PROVED
CT_RUN_BRIDGE=NOT_PROVED
PI_NONNORMALITY=NOT_CLAIMED
```
