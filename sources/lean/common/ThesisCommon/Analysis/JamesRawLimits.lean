import ThesisCommon.Analysis.JamesRawPaths

/-! A scalar sequence with bounded finite James variation converges. Its
limit-subtracted sequence belongs to the genuine null-sequence James space.
-/
noncomputable section
open Filter Topology
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem jamesRawPath_cauchy (a : ℕ → 𝕜) {C : ℝ}
    (hbound : ∀ s : JamesPath, ‖jamesRawPath p s a‖ ≤ C) : CauchySeq a := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := jamesRawPath_far_small p hp a hbound hε
  refine ⟨N + 1, fun n hn m hm => ?_⟩
  have hpair (i j : ℕ) (hi : N < i) (hij : i < j) : dist (a i) (a j) < ε := by
    have hb := PiLp.norm_apply_le (jamesRawPath p (JamesPath.two i j hij) a) (0 : Fin 1)
    have ht := hN (JamesPath.two i j hij) (by simpa [JamesPath.two] using hi)
    simpa [jamesRawPath_apply, JamesPath.two, dist_eq_norm] using hb.trans_lt ht
  rcases lt_trichotomy n m with hnm | rfl | hmn
  · exact hpair n m (by omega) hnm
  · simpa using hε
  · rw [dist_comm]
    exact hpair m n (by omega) hmn

include hp in
theorem jamesRawPath_exists_limit (a : ℕ → 𝕜) {C : ℝ}
    (hbound : ∀ s : JamesPath, ‖jamesRawPath p s a‖ ≤ C) :
    ∃ L : 𝕜, Tendsto a atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (jamesRawPath_cauchy p hp a hbound)

def jamesNullSubtract (a : ℕ → 𝕜) (L : 𝕜) (hlim : Tendsto a atTop (𝓝 L)) : CZeroSum 𝕜 where
  toFun n := a n - L
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    simpa only [sub_self] using hlim.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L))

theorem jamesNullSubtract_path (a : ℕ → 𝕜) (L : 𝕜) (hlim : Tendsto a atTop (𝓝 L))
    (s : JamesPath) : jamesPathMap 𝕜 p s (jamesNullSubtract a L hlim) = jamesRawPath p s a := by
  ext j
  change (a (s.index j.castSucc) - L) - (a (s.index j.succ) - L) = _
  simp only [jamesRawPath_apply]
  abel

def jamesOfConvergentVariation (a : ℕ → 𝕜) (L : 𝕜) (hlim : Tendsto a atTop (𝓝 L))
    {C : ℝ} (hbound : ∀ s : JamesPath, ‖jamesRawPath p s a‖ ≤ C) : JamesSequenceSpace 𝕜 p :=
  ⟨jamesNullSubtract a L hlim, ⟨C, by
    rintro _ ⟨s, rfl⟩
    dsimp only
    rw [jamesNullSubtract_path]
    exact hbound s⟩⟩

@[simp] theorem jamesOfConvergentVariation_apply (a : ℕ → 𝕜) (L : 𝕜)
    (hlim : Tendsto a atTop (𝓝 L)) {C : ℝ}
    (hbound : ∀ s : JamesPath, ‖jamesRawPath p s a‖ ≤ C) (n : ℕ) :
    jamesOfConvergentVariation p a L hlim hbound n = a n - L := rfl

theorem jamesOfConvergentVariation_norm_le (a : ℕ → 𝕜) (L : 𝕜)
    (hlim : Tendsto a atTop (𝓝 L)) {C : ℝ}
    (hbound : ∀ s : JamesPath, ‖jamesRawPath p s a‖ ≤ C) :
    ‖jamesOfConvergentVariation p a L hlim hbound‖ ≤ C := by
  apply JamesSequenceSpace.norm_le
  intro s
  change ‖jamesPathMap 𝕜 p s (jamesNullSubtract a L hlim)‖ ≤ C
  rw [jamesNullSubtract_path]
  exact hbound s

end ThesisCommon
