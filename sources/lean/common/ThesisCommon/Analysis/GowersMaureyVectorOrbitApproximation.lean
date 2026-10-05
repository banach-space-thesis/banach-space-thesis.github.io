import ThesisCommon.Analysis.GowersMaureyCodedPairNormUpper
import ThesisCommon.Analysis.GowersMaureyCodedPairDetection
import ThesisCommon.Analysis.GowersMaureySpecialGrowthContradiction

/-! The source's Lemma 8 for the actual constructed shift space. Every
bounded operator on an actual subspace admits vectorwise approximation
on a sufficiently late interval-norm unit ball by a finite spread orbit.
The coefficient budget and square of spread parameters are both explicit.
No finite-spread approximation hypothesis is assumed. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem no_block_orbit_counterexamples {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y)
    (hne : ∀ i, u.vector i ≠ 0) (T : Y →L[𝕜] ShiftSpace D)
    (q : ℕ → ℕ) (hq : StrictMono q) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖) : False := by
  obtain ⟨t,_,ht⟩ := D.exists_special_pair_lower_gt_upper
    (L := ‖T‖) hε (specialPairContraction_pos T) 0
  let k := D.j (2*t)
  have hk : 0 < k := D.j_positive _
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let η := ε/(32*(k : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨d,_,_⟩ := exists_detecting_special_RIS_family u hne T q hq hε hsep hη k hk
  have hbudget : (k : ℝ)*η ≤ ε/32 := by
    dsimp [η]
    have he : (k : ℝ)*(ε/(32*(k : ℝ))) = ε/32 := by field_simp
    exact he.le
  have hlo := d.operator_sum_lower_bound (show k ∈ D.specialSizes from ⟨t,rfl⟩)
    hη.le hbudget
  have hnorm : ‖∑ i, (d.pair i).inSubspace‖ = implicitNorm D (∑ i, (d.pair i).vector) := by
    change ‖((∑ i, (d.pair i).inSubspace : Y) : ShiftSpace D)‖ = _
    simp only [Submodule.coe_sum, DetectingPair.inSubspace]
    rw [← map_sum,denseEmbedding_norm]
    rfl
  have hup := T.le_opNorm (∑ i, (d.pair i).inSubspace)
  rw [hnorm] at hup
  have hup' := hup.trans (mul_le_mul_of_nonneg_left (d.sum_norm_le) (norm_nonneg T))
  have hfinal : (k : ℝ)*ε/(32*Real.sqrt (logarithmicWeight k)) ≤
      ‖T‖*(3/specialPairContraction T)*(k : ℝ)/logarithmicWeight k := by
    convert hlo.trans hup' using 1; ring
  exact (not_le_of_gt ht) hfinal

theorem exists_vectorwise_spread_orbit_approximation (D : ConstructionData 𝕜)
    (Y : Submodule 𝕜 (ShiftSpace D)) (T : Y →L[𝕜] ShiftSpace D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∀ x : C00 𝕜, ∀ hx : denseEmbedding D x ∈ Y,
      intervalNorm D r x ≤ 1 → x ∈ afterCutoff r →
      ∃ z ∈ spreadVectorOrbit D x r, ‖T ⟨denseEmbedding D x,hx⟩-z‖ < ε := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨u,q,hq,_,hne,_,hsep⟩ := exists_block_orbit_counterexamples D Y T hε h
  exact no_block_orbit_counterexamples u hne T q hq hε hsep

end ThesisCommon.GowersMaurey
