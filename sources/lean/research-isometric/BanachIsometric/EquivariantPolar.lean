import BanachIsometric.StabilizerLipschitz
import BanachIsometric.LocalCovarianceFactor
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A Lipschitz left-equivariant polar correction near the unitary group

All operators act on the original finite-dimensional real inner-product
space. The norm identity for `T* T` bounds the whole Gram neighbourhood, and
the local whitening factor constructs an actual unitary correction. Its left
equivariance follows because the Gram operator is unchanged by left unitary
multiplication. No global square-root or tubular-retraction theorem is assumed.
-/

namespace BanachIsometric

open Set Filter
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def operatorGram (T : E →L[ℝ] E) : E →L[ℝ] E := star T * T

theorem operatorGram_left_unitary (h T : E →L[ℝ] E) (hh : h ∈ unitary (E →L[ℝ] E)) :
    operatorGram (h * T) = operatorGram T := by
  have hh' : star h * h = 1 := (unitary.mem_iff.mp hh).1
  calc
    _ = star T * ((star h * h) * T) := by simp only [operatorGram, star_mul, mul_assoc]
    _ = operatorGram T := by rw [hh', one_mul]; rfl

set_option maxHeartbeats 800000 in
theorem exists_lipschitz_equivariant_polar_correction :
    ∃ U : Set (E →L[ℝ] E), ∃ P : (E →L[ℝ] E) → (E →L[ℝ] E), ∃ L : ℝ≥0,
      IsOpen U ∧ (unitary (E →L[ℝ] E) : Set _) ⊆ U ∧ LipschitzOnWith L P U ∧
      (∀ T ∈ U, P T ∈ unitary (E →L[ℝ] E)) ∧
      (∀ h ∈ unitary (E →L[ℝ] E), P h = h) ∧
      (∀ h ∈ unitary (E →L[ℝ] E), ∀ T, P (h * T) = h * P T) ∧
      (∀ h ∈ unitary (E →L[ℝ] E), ∀ T ∈ U, h * T ∈ U) := by
  classical
  obtain ⟨Q, V, KQ, hV, h1V, hQ1, hQLip, _, hQWhite⟩ :=
    exists_lipschitz_local_covarianceWhitening (A := E →L[ℝ] E)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h1V)
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  let U : Set (E →L[ℝ] E) := operatorGram ⁻¹' Metric.ball 1 δ
  let P : (E →L[ℝ] E) → (E →L[ℝ] E) := fun T => T * Q (operatorGram T)
  have hGcont : Continuous (operatorGram : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    (continuous_star : Continuous (star : (E →L[ℝ] E) → (E →L[ℝ] E))).mul continuous_id
  have hU : IsOpen U := Metric.isOpen_ball.preimage hGcont
  have hGV : ∀ T ∈ U, operatorGram T ∈ V := by
    intro T hT
    have hd : dist (operatorGram T) (1 : E →L[ℝ] E) < δ := hT
    apply hball
    change dist (operatorGram T) (1 : E →L[ℝ] E) < ε
    exact hd.trans_le hδε
  have hGdist : ∀ T ∈ U, dist (operatorGram T) 1 ≤ 1 := by
    intro T hT
    have hd : dist (operatorGram T) (1 : E →L[ℝ] E) < δ := hT
    exact hd.le.trans hδ1
  have hTBound : ∀ T ∈ U, ‖T‖ ≤ (2 : ℝ≥0) := by
    intro T hT
    have hGNorm : ‖operatorGram T‖ ≤ 2 :=
      (norm_le_norm_add_const_of_dist_le (hGdist T hT)).trans (by
        have hnorm : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        linarith)
    change ‖T.adjoint.comp T‖ ≤ 2 at hGNorm
    rw [ContinuousLinearMap.norm_adjoint_comp_self] at hGNorm
    have hn := norm_nonneg T
    change ‖T‖ ≤ 2
    nlinarith
  have hQBound : ∀ T ∈ U, ‖Q (operatorGram T)‖ ≤ (1 + KQ : ℝ≥0) := by
    intro T hT
    have hd : dist (Q (operatorGram T)) 1 ≤ KQ := by
      have h := hQLip.dist_le_mul (operatorGram T) (hGV T hT) 1 h1V
      rw [hQ1] at h
      exact h.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hGdist T hT) KQ.coe_nonneg)
    have hnorm : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    change ‖Q (operatorGram T)‖ ≤ 1 + (KQ : ℝ)
    exact (norm_le_norm_add_const_of_dist_le hd).trans (by linarith)
  have hId : LipschitzOnWith 1 (fun T : E →L[ℝ] E => T) U := LipschitzWith.id.lipschitzOnWith
  have hStar : LipschitzOnWith 1 (star : (E →L[ℝ] E) → (E →L[ℝ] E)) U :=
    ContinuousLinearMap.adjoint.lipschitz.lipschitzOnWith
  have hGLip : LipschitzOnWith ((2 : ℝ≥0) * 1 + 1 * 2) operatorGram U :=
    lipschitzOnWith_ring_mul_of_norm_bounds hStar hId
      (fun T hT => by
        change ‖T.adjoint‖ ≤ (2 : ℝ≥0)
        rw [LinearIsometryEquiv.norm_map]
        exact hTBound T hT) hTBound
  have hQG : LipschitzOnWith (KQ * ((2 : ℝ≥0) * 1 + 1 * 2))
      (fun T => Q (operatorGram T)) U := hQLip.comp hGLip hGV
  have hPLip := lipschitzOnWith_ring_mul_of_norm_bounds hId hQG hTBound hQBound
  refine ⟨U, P, 2 * (KQ * (2 * 1 + 1 * 2)) + 1 * (1 + KQ), hU, ?_, hPLip, ?_, ?_, ?_, ?_⟩
  · intro h hh
    change dist (star h * h) 1 < δ
    rw [(unitary.mem_iff.mp hh).1, dist_self]
    exact hδ
  · intro T hT
    have hself : IsSelfAdjoint (operatorGram T) := by
      apply isSelfAdjoint_iff.mpr
      simp only [operatorGram, star_mul, star_star]
    obtain ⟨hQSelf, hWhite⟩ := hQWhite (operatorGram T) (hGV T hT) hself
    have hLeft : star (P T) * P T = 1 := by
      have hWhite' : Q (operatorGram T) * operatorGram T * Q (operatorGram T) = 1 := by
        simpa only [hQSelf.star_eq] using hWhite
      change star (T * Q (operatorGram T)) * (T * Q (operatorGram T)) = 1
      rw [star_mul, hQSelf.star_eq]
      simpa only [operatorGram, mul_assoc] using hWhite'
    have hLinLeft : Function.LeftInverse
        (fun x : E => (star (P T) : E →L[ℝ] E) x) (fun x : E => P T x) := by
      intro x
      exact congrArg (fun A : E →L[ℝ] E => A x) hLeft
    have hSurj : Function.Surjective (P T) :=
      (LinearMap.injective_iff_surjective (f := (P T).toLinearMap)).mp hLinLeft.injective
    refine ⟨hLeft, ?_⟩
    apply ContinuousLinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hSurj y
    change P T (star (P T) (P T x)) = P T x
    exact congrArg (P T) (hLinLeft x)
  · intro h hh
    change h * Q (star h * h) = h
    rw [(unitary.mem_iff.mp hh).1, hQ1, mul_one]
  · intro h hh T
    change (h * T) * Q (operatorGram (h * T)) = h * (T * Q (operatorGram T))
    rw [operatorGram_left_unitary h T hh, mul_assoc]
  · intro h hh T hT
    change dist (operatorGram (h * T)) (1 : E →L[ℝ] E) < δ
    rw [operatorGram_left_unitary h T hh]
    exact hT

end
end BanachIsometric
