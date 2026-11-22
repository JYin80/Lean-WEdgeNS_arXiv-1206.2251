module

public import WEdgeNS

public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace WEdgeNS

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `WEdgeNS` named in its proof
(`E1`, `E1_not_tight`, `E1_no_limit` in `WEdgeNS/E1/Necessity.lean` and `E2` in
`WEdgeNS/E2/Sufficiency.lean`). The definitions that occur in the statements are those of
`WEdgeNS/Model/Wigner.lean`; `Challenge.lean` repeats them verbatim, and Comparator checks that
the two copies agree.
-/

/-- **Theorem 1.2, necessity, (1.6).** If condition (1.4) fails, that is, if `s⁴ P(|x₁₂| ≥ s)` does
not tend to `0`, then `P(λ_N ≥ 3) ≥ c` for some `c > 0` and infinitely many `N`; equivalently
`limsup_N P(λ_N ≥ 3) > 0`. -/
theorem necessity (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | 3 ≤ lambdaMax (wignerMatrix N ω)}).toReal :=
  E1 ν ν' hW h14

/-- **Theorem 1.2, necessity: no tightness.** If (1.4) fails, there is `c > 0` such that
`P(|N^{2/3}(λ_N - 2)| > K) ≥ c` for every `K` and infinitely many `N`. -/
theorem necessity_not_tight (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ,
      ∃ᶠ N in atTop, c ≤ (entryLaw ν ν' N {ω | K < |edgeScaled N ω|}).toReal :=
  E1_not_tight ν ν' hW h14

/-- **Theorem 1.2, necessity: no limit.** If (1.4) fails, `N^{2/3}(λ_N - 2)` converges in
distribution to no probability law on `ℝ`; in particular not to the Tracy–Widom law. -/
theorem necessity_no_limit (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : ¬ TailCond ν) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ s : ℝ, ContinuousAt (cdf μ) s →
        Tendsto (fun N => edgeCdf ν ν' N s) atTop (𝓝 (cdf μ s)) :=
  E1_no_limit ν ν' hW h14

/-- **Theorem 1.2, sufficiency, in the GOE-comparison form (4.9).** If (1.4) holds, there are
`δ > 0` and a sequence `ε_N → 0` such that, for all large `N` and all `s ∈ ℝ`,
`P_GOE(X_N ≤ s - N^{-δ}) - ε_N ≤ P(X_N ≤ s) ≤ P_GOE(X_N ≤ s + N^{-δ}) + ε_N`, where
`X_N = N^{2/3}(λ_N - 2)`. Both `δ` and the sequence `ε` are chosen before `N`, and `ε` does not
depend on `s`. -/
theorem sufficiency (ν ν' : Measure ℝ) (hW : WignerLaws ν ν') (h14 : TailCond ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ N in atTop, ∀ s : ℝ,
      goeCdf N (s - (N : ℝ) ^ (-δ)) - ε N ≤ edgeCdf ν ν' N s ∧
      edgeCdf ν ν' N s ≤ goeCdf N (s + (N : ℝ) ^ (-δ)) + ε N :=
  E2 ν ν' hW h14

end WEdgeNS
