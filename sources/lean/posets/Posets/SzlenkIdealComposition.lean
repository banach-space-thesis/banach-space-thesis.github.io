import Posets.SzlenkIdealImage

/-! Scalar and two-sided composition stability of the actual Szlenk bound.
No completeness, rank convention, or asserted ideal property is used. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 D E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem weakStarAdjoint_norm_sub_le (T : E →L[𝕜] F) (a b : WeakDual 𝕜 F) :
    ‖WeakDual.toStrongDual (weakStarAdjoint T a) -
      WeakDual.toStrongDual (weakStarAdjoint T b)‖ ≤
      ‖T‖ * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ := by
  change ‖(WeakDual.toStrongDual a).comp T - (WeakDual.toStrongDual b).comp T‖ ≤ _
  rw [← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

theorem adjointUnitBall_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    adjointUnitBall (S.comp T) = weakStarAdjoint T '' adjointUnitBall S := by
  unfold adjointUnitBall
  rw [Set.image_image]
  rfl

theorem OperatorSzlenkBound.precomp {T : E →L[𝕜] F} {α : Ordinal}
    (h : OperatorSzlenkBound T α) (U : D →L[𝕜] E) :
    OperatorSzlenkBound (T.comp U) α := by
  rw [OperatorSzlenkBound, adjointUnitBall_comp]
  apply HasSzlenkBound.image h (adjointUnitBall_isCompact T)
    (weakStarAdjoint U) (weakStarAdjoint_continuous U) (L := ‖U‖ + 1) (by positivity)
  intro a b
  apply (weakStarAdjoint_norm_sub_le U a b).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem adjointUnitBall_smul (c : 𝕜) (T : E →L[𝕜] F) :
    adjointUnitBall (c • T) = (fun φ => c • φ) '' adjointUnitBall T := by
  unfold adjointUnitBall
  rw [Set.image_image]
  apply Set.image_congr
  intro φ _
  apply DFunLike.ext
  intro x
  change φ (c • T x) = c • φ (T x)
  exact map_smul φ c (T x)

theorem HasSzlenkBound.smul {K : Set (WeakDual 𝕜 E)} {α : Ordinal}
    (h : HasSzlenkBound K α) (hK : IsCompact K) (c : 𝕜) :
    HasSzlenkBound ((fun φ => c • φ) '' K) α := by
  apply h.image hK (fun φ : WeakDual 𝕜 E => c • φ)
    (continuous_const_smul c) (L := ‖c‖ + 1) (by positivity)
  intro a b
  change ‖c • WeakDual.toStrongDual a - c • WeakDual.toStrongDual b‖ ≤ _
  rw [← smul_sub c (WeakDual.toStrongDual a) (WeakDual.toStrongDual b), norm_smul]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

theorem OperatorSzlenkBound.smul {T : E →L[𝕜] F} {α : Ordinal}
    (h : OperatorSzlenkBound T α) (c : 𝕜) : OperatorSzlenkBound (c • T) α := by
  rw [OperatorSzlenkBound, adjointUnitBall_smul]
  exact HasSzlenkBound.smul h (adjointUnitBall_isCompact T) c

theorem adjointUnitBall_comp_subset (S : F →L[𝕜] G) (T : E →L[𝕜] F)
    (hS : ‖S‖ ≤ 1) : adjointUnitBall (S.comp T) ⊆ adjointUnitBall T := by
  rintro x ⟨φ, hφ, rfl⟩
  refine ⟨weakStarAdjoint S φ, ?_, rfl⟩
  have hφnorm : ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
    simpa only [weakStarUnitBall, Set.mem_preimage, Metric.mem_closedBall,
      dist_zero_right] using hφ
  change ‖(WeakDual.toStrongDual φ).comp S - 0‖ ≤ 1
  rw [sub_zero]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hφnorm hS (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

theorem OperatorSzlenkBound.postcomp {T : E →L[𝕜] F} {α : Ordinal}
    (h : OperatorSzlenkBound T α) (V : F →L[𝕜] G) :
    OperatorSzlenkBound (V.comp T) α := by
  let c : 𝕜 := ((‖V‖ + 1 : ℝ) : 𝕜)
  have hcpos : 0 < ‖V‖ + 1 := by positivity
  have hcnorm : ‖c‖ = ‖V‖ + 1 := by
    change ‖((‖V‖ + 1 : ℝ) : 𝕜)‖ = _
    rw [RCLike.norm_ofReal, abs_of_pos hcpos]
  have hcne : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcnorm]; exact hcpos.ne')
  have hsmall : ‖c⁻¹ • V‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hcnorm]
    exact (inv_mul_le_iff₀ hcpos).mpr (by linarith)
  have hs : OperatorSzlenkBound ((c⁻¹ • V).comp (c • T)) α :=
    HasSzlenkBound.subset (h.smul c) (adjointUnitBall_comp_subset _ _ hsmall)
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, mul_inv_cancel₀ hcne, one_smul] using hs

theorem OperatorSzlenkBound.comp {T : E →L[𝕜] F} {α : Ordinal}
    (h : OperatorSzlenkBound T α) (U : D →L[𝕜] E) (V : F →L[𝕜] G) :
    OperatorSzlenkBound (V.comp (T.comp U)) α :=
  (h.precomp U).postcomp V

theorem szlenkDeriv_singleton (φ : WeakDual 𝕜 E) {ε : ℝ} (hε : 0 < ε) :
    szlenkDeriv ε {φ} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 Set.univ isOpen_univ (Set.mem_univ x)
  have ha' : a = φ := ha.1
  have hb' : b = φ := hb.1
  rw [ha', hb', sub_self, norm_zero] at hab
  exact (not_lt_of_ge hε.le) hab

theorem operatorSzlenkBound_zero {α : Ordinal} (hα : 1 ≤ α) :
    OperatorSzlenkBound (0 : E →L[𝕜] F) α := by
  apply OperatorSzlenkBound.mono (α := 1) ?_ hα
  have hball : adjointUnitBall (0 : E →L[𝕜] F) ⊆ {0} := by
    rintro x ⟨φ, _, rfl⟩
    apply DFunLike.ext
    intro z
    change φ (0 : F) = 0
    exact map_zero φ
  apply HasSzlenkBound.subset ?_ hball
  intro ε hε
  rw [← Ordinal.succ_zero, szlenkIterate_succ, szlenkIterate_zero]
  exact szlenkDeriv_singleton _ hε

theorem zero_mem_szlenkOperatorClass (α : Ordinal) :
    (0 : E →L[𝕜] F) ∈ SzlenkOperatorClass α :=
  operatorSzlenkBound_zero (Order.one_le_iff_pos.mpr
    (Ordinal.opow_pos α Ordinal.omega0_pos))

end Posets
