import ThesisCommon.Analysis.FilterFunctionalCharge
import ThesisCommon.Analysis.InfinityFiniteApproximation

/-! The total variation of the constructed finitely additive charge controls
the functional on every supported bounded family. The proof first treats
finite-valued families, then uses genuine uniform approximation. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ : Type*} [RCLike 𝕜]

theorem functionalCharge_finite_range_bound
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜)
    (y : lp (fun _ : Γ => 𝕜) ∞) (hy : (Set.range (fun γ => y γ)).Finite)
    {A : Set Γ} (hsupp : ∀ γ ∉ A, y γ = 0) :
    ‖φ y‖ ≤ (functionalCharge φ).variation A * ‖y‖ := by
  classical
  let S : Set 𝕜 := Set.range (fun γ => y γ) \ {0}
  have hS : S.Finite := hy.diff
  letI := hS.fintype
  let e := Fintype.equivFin S
  let c : Fin (Fintype.card S) → 𝕜 := fun i => (e.symm i).val
  let B : Fin (Fintype.card S) → Set Γ := fun i => {γ | y γ = c i}
  have hc0 : ∀ i, c i ≠ 0 := fun i => (e.symm i).property.2
  have hB : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro γ hi hj
    apply hij
    apply e.symm.injective
    exact Subtype.ext (hi.symm.trans hj)
  have hBA : ∀ i, B i ⊆ A := by
    intro i γ hγ
    by_contra hn
    exact hc0 i (hγ.symm.trans (hsupp γ hn))
  have hc : ∀ i, ‖c i‖ ≤ ‖y‖ := by
    intro i
    obtain ⟨γ, hγ⟩ := (e.symm i).property.1
    simpa only [hγ] using lp.norm_apply_le_norm ENNReal.top_ne_zero y γ
  have hrepr : y = ∑ i, c i • infinityIndicator (𝕜 := 𝕜) (B i) := by
    ext γ
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      infinityIndicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hγ : y γ = 0
    · have hn : ∀ i, γ ∉ B i := fun i hi => hc0 i (hi.symm.trans hγ)
      simp only [if_neg (hn _), Finset.sum_const_zero, hγ]
    · let z : S := ⟨y γ, ⟨⟨γ, rfl⟩, hγ⟩⟩
      let i := e z
      have hci : c i = y γ := congrArg Subtype.val (e.symm_apply_apply z)
      have hi : γ ∈ B i := hci.symm
      rw [Finset.sum_eq_single i]
      · simpa only [if_pos hi] using hci.symm
      · intro j _ hji
        have hj : γ ∉ B j := fun hj => Set.disjoint_left.mp (hB hji.symm) hi hj
        simp only [if_neg hj]
      · simp
  calc
    ‖φ y‖ = ‖φ (∑ i, c i • infinityIndicator (B i))‖ := congrArg (fun z => ‖φ z‖) hrepr
    _ ≤ (functionalCharge φ).variation A * ‖y‖ :=
      functionalCharge_simple_bound φ B hB hBA c (norm_nonneg y) hc

/-- The quantitative support estimate for an arbitrary bounded family.
All finite variation and approximation assertions are proved independently. -/
theorem functionalCharge_support_bound
    (φ : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] 𝕜)
    (x : lp (fun _ : Γ => 𝕜) ∞) {A : Set Γ}
    (hsupp : ∀ γ ∉ A, x γ = 0) :
    ‖φ x‖ ≤ (functionalCharge φ).variation A * ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < ‖φ‖ + 1 := by positivity
  obtain ⟨y, hy, hzero, hnorm, hclose⟩ :=
    infinity_exists_finite_range_approximation x (div_pos hε hden)
  have hysupp : ∀ γ ∉ A, y γ = 0 := fun γ hγ => hzero γ (hsupp γ hγ)
  have hybound := functionalCharge_finite_range_bound φ y hy hysupp
  have herror : ‖φ (x - y)‖ ≤ ε := by
    calc
      _ ≤ ‖φ‖ * ‖x - y‖ := φ.le_opNorm _
      _ ≤ (‖φ‖ + 1) * (ε / (‖φ‖ + 1)) :=
        mul_le_mul (by linarith) hclose.le (norm_nonneg _) hden.le
      _ = ε := by field_simp
  have htriangle : ‖φ x‖ ≤ ‖φ (x - y)‖ + ‖φ y‖ := by
    simpa only [map_sub, sub_add_cancel] using norm_add_le (φ (x - y)) (φ y)
  have hmain := mul_le_mul_of_nonneg_left hnorm ((functionalCharge φ).variation_nonneg A)
  linarith

end ThesisCommon
