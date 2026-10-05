import ThesisCommon.Analysis.LpCoordinateDualGrowth

/-! Every operator from a space with an actual ell-one dual into a scalar
finite-p sum has separable range. The proof gives countable coordinate
support directly, using weak nullity of coordinate functionals and Schur. -/
noncomputable section
open Filter Topology TopologicalSpace
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 Γ X I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lp_countable_coordinate_functionals_of_dual_equiv_ellOne
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : Γ => 𝕜) p) :
    {γ | (lpCoordinate (𝕜 := 𝕜) p γ).comp T ≠ 0}.Countable :=
  countable_support_of_ellOne_equiv_weak_null d
    (fun γ => (lpCoordinate (𝕜 := 𝕜) p γ).comp T)
    (lp_coordinate_comp_weak_null p hp T)

theorem lp_operator_countable_support_of_dual_equiv_ellOne
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : Γ => 𝕜) p) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ x γ, γ ∉ Δ → T x γ = 0 := by
  refine ⟨{γ | (lpCoordinate (𝕜 := 𝕜) p γ).comp T ≠ 0},
    lp_countable_coordinate_functionals_of_dual_equiv_ellOne d p hp T, ?_⟩
  intro x γ hγ
  have hz : (lpCoordinate (𝕜 := 𝕜) p γ).comp T = 0 := not_not.mp hγ
  exact DFunLike.congr_fun hz x

theorem isSeparable_lp_range_of_countable_support
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : Γ => 𝕜) p)
    (Δ : Set Γ) (hΔ : Δ.Countable) (hT : ∀ x γ, γ ∉ Δ → T x γ = 0) :
    IsSeparable (Set.range T) := by
  classical
  letI : Countable Δ := hΔ.to_subtype
  letI := lp_separableSpace_of_countable (𝕜 := 𝕜) (Γ := Δ) (X := 𝕜) p hp
  let e : Δ ↪ Γ := Function.Embedding.subtype Δ
  let J : lp (fun _ : Δ => 𝕜) p →L[𝕜] lp (fun _ : Γ => 𝕜) p := lpExtend p e
  apply (isSeparable_range J.continuous).mono
  rintro _ ⟨x, rfl⟩
  refine ⟨lpRestrict (𝕜 := 𝕜) p e (T x), ?_⟩
  apply lp.ext
  funext γ
  by_cases hγ : γ ∈ Δ
  · exact lpExtend_apply_image (𝕜 := 𝕜) (p := p) e (lpRestrict (𝕜 := 𝕜) p e (T x)) ⟨γ, hγ⟩
  · have hr : ¬ ∃ i : Δ, e i = γ := by rintro ⟨i, hi⟩; exact hγ (hi ▸ i.property)
    change lpExtend (𝕜 := 𝕜) p e (lpRestrict (𝕜 := 𝕜) p e (T x)) γ = T x γ
    simp only [lpExtend, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Function.extend_apply' _ _ _ hr, Pi.zero_apply, hT x γ hγ]

theorem isSeparable_lp_range_of_dual_equiv_ellOne
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : Γ => 𝕜) p) : IsSeparable (Set.range T) := by
  obtain ⟨Δ, hΔ, hT⟩ := lp_operator_countable_support_of_dual_equiv_ellOne d p hp T
  exact isSeparable_lp_range_of_countable_support p hp T Δ hΔ hT

end ThesisCommon
