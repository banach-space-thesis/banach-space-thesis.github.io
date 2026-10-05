import ThesisCommon.Analysis.GowersMaureyVectorOrbitApproximation

/-! The literal vector orbit in Lemma 8 is the evaluation of the actual
finite operator orbit. Positive rescaling gives the interval-norm-eight
local input used by the subsequent compact-convex argument. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_operator_of_mem_spreadVectorOrbit (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) (x : C00 𝕜) (hx : denseEmbedding D x ∈ Y)
    (m : ℕ) {z : ShiftSpace D} (hz : z ∈ spreadVectorOrbit D x m) :
    ∃ V ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜)
      (fun a : spreadParameterSquare m => (completedSpread D a.val.1 a.val.2).comp Y.subtypeL) m,
      V ⟨denseEmbedding D x,hx⟩ = z := by
  classical
  rw [spreadVectorOrbit,finiteParameterOrbit_eq] at hz
  obtain ⟨c,hc,rfl⟩ := hz
  refine ⟨∑ a, c a • ((completedSpread D a.val.1 a.val.2).comp Y.subtypeL),
    ⟨c,hc,rfl⟩,?_⟩
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,completedSpread_denseEmbedding]
  rfl

theorem exists_local_operator_orbit_approximation (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) (T : Y →L[𝕜] ShiftSpace D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : C00 𝕜, ∀ hx : denseEmbedding D x ∈ Y,
      intervalNorm D m x ≤ 8 → x ∈ afterCutoff m →
      ∃ V ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜)
        (fun a : spreadParameterSquare m => (completedSpread D a.val.1 a.val.2).comp Y.subtypeL) m,
        ‖(T-V) ⟨denseEmbedding D x,hx⟩‖ ≤ 8*ε := by
  obtain ⟨m,hm,hlocal⟩ := exists_vectorwise_spread_orbit_approximation D Y T hε
  refine ⟨m,hm,?_⟩
  intro x hx hn ht
  let y := (1/8 : ℝ) • x
  have he : y = ((1/8 : ℝ) : 𝕜) • x := by
    ext n
    simp only [y,Finsupp.smul_apply,smul_eq_mul,RCLike.real_smul_eq_coe_mul]
  have hy : denseEmbedding D y ∈ Y := by
    rw [he,map_smul]
    exact Y.smul_mem _ hx
  have hyn : intervalNorm D m y ≤ 1 := by
    dsimp only [y]
    rw [seminorm_real_smul,abs_of_pos (by norm_num : (0 : ℝ)<1/8)]
    linarith
  have hyt : y ∈ afterCutoff m := (afterCutoff m).smul_mem (1/8 : ℝ) ht
  obtain ⟨z,hz,hnear⟩ := hlocal y hy hyn hyt
  obtain ⟨V,hV,hVz⟩ := exists_operator_of_mem_spreadVectorOrbit D Y y hy m hz
  refine ⟨V,hV,?_⟩
  have hys : (⟨denseEmbedding D y,hy⟩ : Y) =
      ((1/8 : ℝ) : 𝕜) • (⟨denseEmbedding D x,hx⟩ : Y) := by
    apply Subtype.ext
    simp only [he,map_smul,Submodule.coe_smul]
  have hb : ‖(T-V) ⟨denseEmbedding D y,hy⟩‖ < ε := by
    simpa only [ContinuousLinearMap.sub_apply,hVz] using hnear
  rw [hys,map_smul,norm_smul,RCLike.norm_ofReal,
    abs_of_pos (by norm_num : (0 : ℝ)<1/8)] at hb
  linarith

end ThesisCommon.GowersMaurey
