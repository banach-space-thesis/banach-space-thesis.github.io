import SurveyStatements.P4DFJPBounds

/-! Ambient contractions preserving the generating set act contractively
on the genuine DFJP gauge space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Metric
open scoped Pointwise

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

namespace DFJPSpace

variable (D : DFJPGaugeData 𝕜 E) (T : E →L[𝕜] E)
variable (hK : ∀ x ∈ D.carrier, T x ∈ D.carrier) (hT : ‖T‖ ≤ 1)

include hK hT

lemma contraction_neighborhood (j : ℤ) :
    ∀ x ∈ dfjpNeighborhood D.carrier j, T x ∈ dfjpNeighborhood D.carrier j := by
  rintro x ⟨u, ⟨k, hk, rfl⟩, v, ⟨w, hw, rfl⟩, rfl⟩
  have hw' : T w ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (T.le_opNorm w).trans ((mul_le_mul hT (mem_closedBall_zero_iff.mp hw)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have heq : T ((2 : ℝ) ^ j • k + (2 : ℝ) ^ (-j) • w) =
      (2 : ℝ) ^ j • T k + (2 : ℝ) ^ (-j) • T w := by
    exact (T.restrictScalars ℝ).map_add _ _ |>.trans
      (congrArg₂ (· + ·) ((T.restrictScalars ℝ).map_smul _ _)
        ((T.restrictScalars ℝ).map_smul _ _))
  rw [heq]
  exact add_mem_add ⟨T k, hK k hk, rfl⟩ ⟨T w, hw', rfl⟩

lemma gauge_contraction (j : ℤ) (x : E) :
    dfjpGauge D.carrier j (T x) ≤ dfjpGauge D.carrier j x := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨r, hr, hrε, y, hy, hxy⟩ := exists_lt_of_gauge_lt
    (dfjpNeighborhood_absorbent D.zero_mem j)
    (lt_add_of_pos_right (dfjpGauge D.carrier j x) hε)
  have hTy := contraction_neighborhood D T hK hT j y hy
  have heq : T x = r • T y := by
    rw [← hxy]
    exact (T.restrictScalars ℝ).map_smul r y
  have hb : dfjpGauge D.carrier j (T x) ≤ r := by
    apply gauge_le_of_mem hr.le
    exact ⟨T y, hTy, heq.symm⟩
  exact hb.trans_lt hrε

lemma contraction_summable (f : DFJPSpace D) :
    Summable (fun j : ℤ => (dfjpGauge D.carrier j (T (inclusion D f))) ^ 2) :=
  (summable_gauge_sq D f).of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun j => pow_le_pow_left₀ (dfjpGauge_nonneg _ _ _)
      (gauge_contraction D T hK hT j (inclusion D f)) 2)

def contractionLinearMap : DFJPSpace D →ₗ[𝕜] DFJPSpace D where
  toFun f := ofSummable D (T (inclusion D f)) (contraction_summable D T hK hT f)
  map_add' f g := by
    apply inclusion_injective D
    simp only [inclusion_ofSummable, map_add]
  map_smul' a f := by
    apply inclusion_injective D
    simp only [inclusion_ofSummable, map_smul, RingHom.id_apply]

@[simp] lemma inclusion_contractionLinearMap (f : DFJPSpace D) :
    inclusion D (contractionLinearMap D T hK hT f) = T (inclusion D f) :=
  inclusion_ofSummable D (T (inclusion D f)) (contraction_summable D T hK hT f)

lemma contractionLinearMap_norm_le (f : DFJPSpace D) :
    ‖contractionLinearMap D T hK hT f‖ ≤ ‖f‖ := by
  have hn : ‖contractionLinearMap D T hK hT f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq, norm_sq]
    simp only [inclusion_contractionLinearMap]
    exact tsum_le_tsum (fun j => pow_le_pow_left₀ (dfjpGauge_nonneg _ _ _)
      (gauge_contraction D T hK hT j (inclusion D f)) 2)
      (contraction_summable D T hK hT f) (summable_gauge_sq D f)
  nlinarith [norm_nonneg (contractionLinearMap D T hK hT f), norm_nonneg f]

def contraction : DFJPSpace D →L[𝕜] DFJPSpace D :=
  (contractionLinearMap D T hK hT).mkContinuous 1
    (fun f => by simpa using contractionLinearMap_norm_le D T hK hT f)

@[simp] lemma inclusion_comp_contraction :
    (inclusion D).comp (contraction D T hK hT) = T.comp (inclusion D) := by
  apply ContinuousLinearMap.ext
  intro f
  exact inclusion_contractionLinearMap D T hK hT f

lemma norm_contraction_le_one : ‖contraction D T hK hT‖ ≤ 1 := by
  apply (contraction D T hK hT).opNorm_le_bound (by norm_num)
  intro f
  simpa using contractionLinearMap_norm_le D T hK hT f

end DFJPSpace

end SurveyStatements.P4
