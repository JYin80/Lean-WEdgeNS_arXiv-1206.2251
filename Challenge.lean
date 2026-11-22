module

public import Mathlib

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace WEdgeNS

/-!
# A necessary and sufficient condition for edge universality of Wigner matrices

This file is the statement of the main result, Theorem 1.2, of

> J. O. Lee and J. Yin, *A necessary and sufficient condition for edge universality of Wigner
> matrices*, Duke Math. J. 163 (2014), arXiv:1206.2251,

for real symmetric Wigner matrices and the largest eigenvalue (`k = 1`), with the definitions it
uses. It imports Mathlib and nothing else. The proofs are in the library `WEdgeNS`;
`Solution.lean` connects each statement below to the theorem of the library that proves it.

## The model

`H_N = N^{-1/2} (x_ij)` is a real symmetric `N × N` matrix whose entries on and above the diagonal
are independent: the `x_ij`, `i < j`, have law `ν` and the `x_ii` have law `ν'` (`entryLaw`,
`wignerMatrix`). `WignerLaws ν ν'` is the hypothesis of Definition 1.1: both laws are probability
measures with finite second moment, `ν` has mean `0` and variance `1`, and `ν'` has mean `0`.
`λ_N` is the largest eigenvalue (`lambdaMax`, the supremum of the real spectrum), and
`edgeCdf ν ν' N` is the distribution function of `N^{2/3}(λ_N - 2)`. `goeCdf N` is the same
distribution function for the GOE, `x_ij ~ N(0, 1)` and `x_ii ~ N(0, 2)`. `TailCond ν` is
condition (1.4), `lim_{s → ∞} s⁴ P(|x₁₂| ≥ s) = 0`.

## The statements

* `sufficiency`: if (1.4) holds, the distribution of `N^{2/3}(λ_N - 2)` is that of the GOE up to a
  shift `N^{-δ}` and an additive error `ε_N → 0` that is uniform in `s`.
* `necessity`, `necessity_not_tight`, `necessity_no_limit`: if (1.4) fails, then
  `limsup_N P(λ_N ≥ 3) > 0`, which is (1.6); `N^{2/3}(λ_N - 2)` is not tight; and it converges in
  distribution to no probability law on `ℝ`.

## Relation to the printed statement

* Only the real symmetric case and `k = 1` are formalized. The joint law of the `k` largest
  eigenvalues for `k ≥ 2` and the complex Hermitian case are not.
* The paper states sufficiency as convergence to the Tracy–Widom law. `sufficiency` is the
  comparison (4.9) with the GOE, from which that convergence follows by the theorem of Tracy and
  Widom for the GOE. Neither the Tracy–Widom law nor this deduction is formalized.
* In (4.9) the paper has the additive error `N^{-δ}`. Under (1.4) alone this is false for every
  `δ > 0` (Remark 4.1 of the revised paper in `paper-revised/`); the statement here has a
  sequence `ε_N → 0`, chosen before `N` and independent of `s`.
* The negation of (1.4) is "`s⁴ P(|x₁₂| ≥ s)` does not tend to `0`"; the limit need not exist.
* The library uses no result of another work as a hypothesis: the local semicircle law, rigidity,
  the Green function comparison and the edge universality results that the paper cites are proved
  in it from Mathlib.
-/

/-! ### Definitions (copied verbatim, in order, from `WEdgeNS/Model/Wigner.lean`) -/

/-- Strictly upper-triangular index pairs `i < j` of an `N × N` matrix. -/
abbrev OffDiag (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

/-- Entry space of Definition 1.1: diagonal entries `x_ii` and upper entries `x_ij`, `i < j`. -/
abbrev Entries (N : ℕ) := (Fin N → ℝ) × (OffDiag N → ℝ)

/-- Joint law of the entries in Definition 1.1: the `x_ii` are i.i.d. with law `ν'`, the `x_ij`
(`i < j`) are i.i.d. with law `ν`, and all of them are independent. -/
noncomputable def entryLaw (ν ν' : Measure ℝ) (N : ℕ) : Measure (Entries N) :=
  (Measure.pi fun _ : Fin N => ν').prod (Measure.pi fun _ : OffDiag N => ν)

/-- The real symmetric Wigner matrix `H_N = N^{-1/2} (x_ij)` of Definition 1.1. -/
noncomputable def wignerMatrix (N : ℕ) (ω : Entries N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (Real.sqrt N)⁻¹ *
    if h : i = j then ω.1 i
    else if h' : i < j then ω.2 ⟨(i, j), h'⟩
    else ω.2 ⟨(j, i), lt_of_le_of_ne (not_lt.mp h') (fun e => h e.symm)⟩

/-- The largest eigenvalue `λ_N` of a real square matrix, as the supremum of its real spectrum. -/
noncomputable def lambdaMax {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

/-- The hypotheses of Definition 1.1 on the off-diagonal law `ν` and the diagonal law `ν'`. -/
structure WignerLaws (ν ν' : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  prob' : IsProbabilityMeasure ν'
  sq_int : Integrable (fun x : ℝ => x ^ 2) ν
  sq_int' : Integrable (fun x : ℝ => x ^ 2) ν'
  mean : ∫ x, x ∂ν = 0
  var : ∫ x, x ^ 2 ∂ν = 1
  mean' : ∫ x, x ∂ν' = 0

/-- Condition (1.4): `s^4 P(|x_12| ≥ s) → 0` as `s → ∞`. -/
def TailCond (ν : Measure ℝ) : Prop :=
  Tendsto (fun s : ℝ => s ^ 4 * (ν {x | s ≤ |x|}).toReal) atTop (𝓝 0)

/-- The rescaled largest eigenvalue `N^{2/3}(λ_N - 2)`. -/
noncomputable def edgeScaled (N : ℕ) (ω : Entries N) : ℝ :=
  (N : ℝ) ^ ((2 : ℝ) / 3) * (lambdaMax (wignerMatrix N ω) - 2)

/-- The distribution function `s ↦ P(N^{2/3}(λ_N - 2) ≤ s)`. -/
noncomputable def edgeCdf (ν ν' : Measure ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  (entryLaw ν ν' N {ω | edgeScaled N ω ≤ s}).toReal

/-- The same distribution function for the GOE, defined after Definition 1.1:
`x_ij ~ N(0, 1)` and `x_ii ~ N(0, 2)`. -/
noncomputable def goeCdf (N : ℕ) (s : ℝ) : ℝ :=
  edgeCdf (gaussianReal 0 1) (gaussianReal 0 2) N s

/-! ### Theorem 1.2 -/

/-- **Theorem 1.2, necessity, (1.6).** If condition (1.4) fails, that is, if `s⁴ P(|x₁₂| ≥ s)` does
not tend to `0`, then `P(λ_N ≥ 3) ≥ c` for some `c > 0` and infinitely many `N`; equivalently
`limsup_N P(λ_N ≥ 3) > 0`. -/
theorem necessity (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | 3 ≤ lambdaMax (wignerMatrix N ω)}).toReal := by
  sorry

/-- **Theorem 1.2, necessity: no tightness.** If (1.4) fails, there is `c > 0` such that
`P(|N^{2/3}(λ_N - 2)| > K) ≥ c` for every `K` and infinitely many `N`. -/
theorem necessity_not_tight (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ,
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | K < |edgeScaled N ω|}).toReal := by
  sorry

/-- **Theorem 1.2, necessity: no limit.** If (1.4) fails, `N^{2/3}(λ_N - 2)` converges in
distribution to no probability law on `ℝ`; in particular not to the Tracy–Widom law. -/
theorem necessity_no_limit (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ s : ℝ, ContinuousAt (cdf μ) s →
        Tendsto (fun N => edgeCdf ν ν' N s) atTop (𝓝 (cdf μ s)) := by
  sorry

/-- **Theorem 1.2, sufficiency, in the GOE-comparison form (4.9).** If (1.4) holds, there are
`δ > 0` and a sequence `ε_N → 0` such that, for all large `N` and all `s ∈ ℝ`,
`P_GOE(X_N ≤ s - N^{-δ}) - ε_N ≤ P(X_N ≤ s) ≤ P_GOE(X_N ≤ s + N^{-δ}) + ε_N`, where
`X_N = N^{2/3}(λ_N - 2)`. Both `δ` and the sequence `ε` are chosen before `N`, and `ε` does not
depend on `s`. -/
theorem sufficiency (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : TailCond ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ N in atTop, ∀ s : ℝ,
      goeCdf N (s - (N : ℝ) ^ (-δ)) - ε N ≤ edgeCdf ν ν' N s ∧
      edgeCdf ν ν' N s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + ε N := by
  sorry

end WEdgeNS
