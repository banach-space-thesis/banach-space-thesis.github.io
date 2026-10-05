import ThesisCommon.Analysis.GowersMaureyIntervalMeasure
import ThesisCommon.Analysis.GowersMaureyRIS

/-! The scaled interval measure and the bound on the interval norm of an
RIS sum used at the start of the source's Lemma 3. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem seminorm_real_smul (p : Seminorm 𝕜 (C00 𝕜)) (r : ℝ) (x : C00 𝕜) :
    p (r • x) = |r| * p x := by
  exact map_smul_eq_mul (p.restrictScalars ℝ) r x

theorem restrict_real_smul (E : Interval) (r : ℝ) (x : C00 𝕜) :
    restrict E (r • x) = r • restrict E x := by
  ext n
  simp only [restrict_apply, Finsupp.smul_apply]
  split_ifs <;> simp

theorem supportInterval_real_smul {r : ℝ} (hr : r ≠ 0) (x : C00 𝕜) :
    supportInterval (r • x) = supportInterval x := by
  unfold supportInterval
  simp only [Finsupp.support_smul_eq hr]

theorem exists_interval_measure_of_intervalNorm_le (D : ConstructionData 𝕜)
    {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 < C) {x : C00 𝕜}
    (hx0 : x ≠ 0) (hx : intervalNorm D N x ≤ C) :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n) ∧
      (∀ n, n ∉ (supportInterval x).set → μ n = 0) ∧
      (∑ n ∈ (supportInterval x).set, μ n) = C ∧
      ∀ E : Interval, E.set ⊆ (supportInterval x).set →
        C / N < implicitNorm D (restrict E x) →
        implicitNorm D (restrict E x) ≤ ∑ n ∈ E.set, μ n := by
  let y := C⁻¹ • x
  have hy0 : y ≠ 0 := smul_ne_zero (inv_ne_zero hC.ne') hx0
  have hy : intervalNorm D N y ≤ 1 := by
    rw [seminorm_real_smul, abs_of_pos (inv_pos.mpr hC), inv_mul_eq_div, div_le_one hC]
    exact hx
  have hsupport : supportInterval y = supportInterval x :=
    supportInterval_real_smul (inv_ne_zero hC.ne') x
  obtain ⟨ν, hνpos, hνsupp, hνtotal, hνdom⟩ :=
    exists_interval_probability_of_intervalNorm_le D hN hy0 hy
  rw [hsupport] at hνsupp hνtotal hνdom
  refine ⟨fun n => C * ν n, fun n => mul_nonneg hC.le (hνpos n), ?_, ?_, ?_⟩
  · intro n hn
    change C * ν n = 0
    rw [hνsupp n hn, mul_zero]
  · rw [← Finset.mul_sum, hνtotal, mul_one]
  · intro E hE hlarge
    have hlarge' : (N : ℝ)⁻¹ < implicitNorm D (restrict E y) := by
      rw [restrict_real_smul, seminorm_real_smul, abs_of_pos (inv_pos.mpr hC),
        inv_mul_eq_div, lt_div_iff₀ hC]
      simpa only [div_eq_mul_inv, mul_comm] using hlarge
    have hdom := hνdom E hE hlarge'
    rw [restrict_real_smul, seminorm_real_smul, abs_of_pos (inv_pos.mpr hC),
      inv_mul_eq_div, div_le_iff₀ hC] at hdom
    rw [← Finset.mul_sum]
    simpa only [mul_comm] using hdom

theorem RISData.intervalNorm_sum_le {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) {n : ℕ} (hn : ∀ i, n ≤ h.size i) :
    intervalNorm D n (∑ i, x i) ≤ N := by
  calc
    _ ≤ ∑ i, intervalNorm D n (x i) := seminorm_sum_le _ _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
      (intervalNorm_mono D (hn i) (x i)).trans (h.norm_bound i)
    _ = N := by simp

end ThesisCommon.GowersMaurey
