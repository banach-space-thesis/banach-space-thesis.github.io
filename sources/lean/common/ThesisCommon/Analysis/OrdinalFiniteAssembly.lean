import ThesisCommon.Analysis.OrdinalUpperDichotomy
import ThesisCommon.Analysis.CompactUpperTriangular
import ThesisCommon.Analysis.SequencePrimariness
import ThesisCommon.Analysis.DualEllOneUpperTriangular

/-! The finite-exponent ordinal sequence assembly. Its independent cited
inputs, base C-PFP and scalar compactness, remain explicit. No original main
target is weakened by adding these hypotheses. -/
noncomputable section
open scoped ENNReal
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α η a : Ordinal.{u}}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem ordinal_lp_finite_hasCPFP_of_compact
    (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 (OrdinalContinuous 𝕜 α) C)
    (hcompact : ∀ S : OrdinalContinuous 𝕜 α →L[𝕜] lp (fun _ : ℕ => 𝕜) p,
      IsCompactOperator S) :
    HasCPFP 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) (4 * C) := by
  rw [show 4 * C = 2 * (2 * C) by ring]
  apply hasCPFP_of_approximate_compressions (by linarith : 1 ≤ 2 * C)
    (fun U => IsLpUpperPart U U)
    (fun U hU => ordinal_lp_upper_dichotomy hD (Or.inr hp1) hC hX U hU)
  intro T ε hε
  obtain ⟨e, U, _, hsmall, hU⟩ := lp_upper_triangular_of_scalar_compact hp hcompact T hε
  exact ⟨lpRestrict p e, lpExtend p e, U, lpRestrict_comp_extend e,
    norm_lpRestrict_le e, norm_lpExtend_le e, hU.self_upperPart, hsmall⟩

theorem ordinal_lp_finite_upfp_primary_of_compact
    (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (hX : HasUPFP 𝕜 (OrdinalContinuous 𝕜 α))
    (hcompact : ∀ S : OrdinalContinuous 𝕜 α →L[𝕜] lp (fun _ : ℕ => 𝕜) p,
      IsCompactOperator S) :
    HasUPFP 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) ∧
      IsPrimary 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) := by
  obtain ⟨C, hC, hX⟩ := hX
  have h : HasUPFP 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) :=
    ⟨4 * C, by linarith, ordinal_lp_finite_hasCPFP_of_compact hD hp hp1 hC hX hcompact⟩
  exact ⟨h, h.lp_isPrimary⟩

variable {I : Type*}

theorem ordinal_lp_finite_hasCPFP_of_dual_equiv_ellOne
    (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    {C : ℝ} (hC : 1 ≤ C) (hX : HasCPFP 𝕜 (OrdinalContinuous 𝕜 α) C)
    (d : (OrdinalContinuous 𝕜 α →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1) :
    HasCPFP 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) (4 * C) := by
  rw [show 4 * C = 2 * (2 * C) by ring]
  apply hasCPFP_of_approximate_compressions (by linarith : 1 ≤ 2 * C)
    (fun U => IsLpUpperPart U U)
    (fun U hU => ordinal_lp_upper_dichotomy hD (Or.inr hp1) hC hX U hU)
  intro T ε hε
  obtain ⟨e, U, _, hsmall, hU⟩ := lp_upper_triangular_of_dual_equiv_ellOne hp d T hε
  exact ⟨lpRestrict p e, lpExtend p e, U, lpRestrict_comp_extend e,
    norm_lpRestrict_le e, norm_lpExtend_le e, hU.self_upperPart, hsmall⟩

theorem ordinal_lp_finite_upfp_primary_of_dual_equiv_ellOne
    (hD : ordinalDerived (Set.Icc 0 α) η = {a}) (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (hX : HasUPFP 𝕜 (OrdinalContinuous 𝕜 α))
    (d : (OrdinalContinuous 𝕜 α →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1) :
    HasUPFP 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) ∧
      IsPrimary 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) := by
  obtain ⟨C, hC, hX⟩ := hX
  have h : HasUPFP 𝕜 (lp (fun _ : ℕ => OrdinalContinuous 𝕜 α) p) :=
    ⟨4 * C, by linarith, ordinal_lp_finite_hasCPFP_of_dual_equiv_ellOne hD hp hp1 hC hX d⟩
  exact ⟨h, h.lp_isPrimary⟩

end ThesisCommon

