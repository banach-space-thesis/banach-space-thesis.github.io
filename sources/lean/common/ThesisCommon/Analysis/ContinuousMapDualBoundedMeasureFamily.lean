import ThesisCommon.Analysis.ContinuousMapDualMeasureFamily
import ThesisCommon.Analysis.SeparableDualCardinality

/-! Keep the maximal-disjoint-family index through the real, complex and
arbitrary-scalar constructions. For separable C(K), this actual family has
cardinality at most continuum. No bound on unrelated representations is assumed. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
attribute [local instance] RingHomInvPair.of_ringEquiv
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]
  [TopologicalSpace.SeparableSpace C(K, ℝ)]
set_option maxHeartbeats 1000000 in
theorem exists_ordered_continuousMapDual_bounded_measure_family :
    ∃ (I : Type) (μ : I → Measure K), Cardinal.mk I ≤ Cardinal.continuum ∧ (∀ i, IsFiniteMeasure (μ i)) ∧
      ∃ d : (C(K, ℝ) →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun i => Lp ℝ 1 (μ i)) 1,
        ∀ φ, 0 ≤ φ ↔ ∀ i, 0 ≤ d φ i := by
  let E := C(K, ℝ) →L[ℝ] ℝ
  obtain ⟨S, hpos, hdis, htotal⟩ := exists_total_positive_disjoint_family (E := E)
  let a : S → E := Subtype.val
  have ha : ∀ i, 0 ≤ a i := fun i => (hpos i i.property).1
  have hd : Pairwise (fun i j : S => |a i| ⊓ |a j| = 0) := by
    intro i j hij
    rw [abs_of_nonneg (ha i), abs_of_nonneg (ha j)]
    exact hdis i.property j.property (fun h => hij (Subtype.ext h))
  have ht : ∀ x : E, 0 ≤ x → (∀ i, x ⊓ a i = 0) → x = 0 := by
    intro x hx hh
    exact htotal x hx (fun e he => hh ⟨e, he⟩)
  let μ : S → Measure K := fun i => positiveContinuousMapRiesz (a i) (ha i)
  let b := alBandIsometryEquiv continuousMapDual_norm_add_of_nonneg a ha hd ht
  let c : lp (fun i => principalBand (a i)) 1 ≃ₗᵢ[ℝ] lp (fun i => Lp ℝ 1 (μ i)) 1 :=
    lebesgueLpCoordinateEquiv (by norm_num)
      (fun i => (continuousMapPrincipalL1Equiv (a i) (ha i)).symm)
  refine ⟨S, μ, (Cardinal.mk_subtype_le S).trans
    (realDual_cardinal_le_continuum C(K, ℝ)), fun i => inferInstance, b.trans c, ?_⟩
  intro φ
  have hc (i : S) : 0 ≤ (b.trans c) φ i ↔ 0 ≤ b φ i := by
    change 0 ≤ (continuousMapPrincipalL1Equiv (a i) (ha i)).symm (b φ i) ↔ 0 ≤ b φ i
    have h := continuousMapPrincipalL1Equiv_nonneg_iff (a i) (ha i)
      ((continuousMapPrincipalL1Equiv (a i) (ha i)).symm (b φ i))
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  exact (alBandIsometryEquiv_nonneg_iff continuousMapDual_norm_add_of_nonneg a ha hd ht φ).trans
    (forall_congr' fun i => (hc i).symm)

set_option maxHeartbeats 1000000 in
theorem exists_continuousMapComplexDual_bounded_measure_family :
    ∃ (I : Type) (μ : I → Measure K), Cardinal.mk I ≤ Cardinal.continuum ∧ (∀ i, IsFiniteMeasure (μ i)) ∧
      Nonempty ((C(K, ℂ) →L[ℂ] ℂ) ≃ₗᵢ[ℂ] lp (fun i => Lp ℂ 1 (μ i)) 1) := by
  obtain ⟨I, μ, hI, hμ, d, hd⟩ := exists_ordered_continuousMapDual_bounded_measure_family (K := K)
  let r : (C(K, ℝ) →L[ℝ] ℝ) ≃ₗᵢ[ℝ] Lp ℝ 1 (sigmaMeasure μ) :=
    d.trans (sigmaL1PartitionEquiv (𝕜 := ℝ) μ).symm
  have hr (φ : C(K, ℝ) →L[ℝ] ℝ) : 0 ≤ r φ ↔ 0 ≤ φ := by
    rw [← sigmaL1PartitionEquiv_nonneg μ]
    change (∀ i, 0 ≤ sigmaL1PartitionEquiv μ ((sigmaL1PartitionEquiv μ).symm (d φ)) i) ↔ _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (hd φ).symm
  let B := continuousMapComplexDualBanachLatticeModel (K := K)
  let b : B.realForm ≃ₗᵢ[ℝ] Lp ℝ 1 (sigmaMeasure μ) :=
    (continuousMapDualRealFormEquiv (K := K)).trans r
  have hb (φ : B.realForm) : 0 ≤ b φ ↔ 0 ≤ φ := by
    change 0 ≤ r (continuousMapDualRealFormEquiv φ) ↔ _
    rw [hr]
    rfl
  exact ⟨I, μ, hI, hμ, ⟨(B.complexL1RepresentationEquiv b hb).trans
    (sigmaL1PartitionEquiv (𝕜 := ℂ) μ)⟩⟩

theorem exists_continuousMapDual_bounded_measure_family (𝕜 : Type*) [RCLike 𝕜] :
    ∃ (I : Type) (μ : I → Measure K), Cardinal.mk I ≤ Cardinal.continuum ∧ (∀ i, IsFiniteMeasure (μ i)) ∧
      Nonempty ((C(K, 𝕜) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] lp (fun i => Lp 𝕜 1 (μ i)) 1) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hr | hc
  · let e := RCLike.realRingEquiv hr
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.realLinearIsometryEquiv hr).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    obtain ⟨I, μ, hI, hμ, d, _⟩ := exists_ordered_continuousMapDual_bounded_measure_family (K := K)
    exact ⟨I, μ, hI, hμ, ⟨continuousMapDualMeasureFamilyScalarTransport e μ d⟩⟩
  · let e := RCLike.complexRingEquiv hc
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.complexLinearIsometryEquiv hc).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    obtain ⟨I, μ, hI, hμ, ⟨d⟩⟩ := exists_continuousMapComplexDual_bounded_measure_family (K := K)
    exact ⟨I, μ, hI, hμ, ⟨continuousMapDualMeasureFamilyScalarTransport e μ d⟩⟩

theorem exists_intervalContinuousDual_bounded_measure_family (𝕜 : Type*) [RCLike 𝕜] :
    ∃ (I : Type) (μ : I → Measure UnitInterval), Cardinal.mk I ≤ Cardinal.continuum ∧ (∀ i, IsFiniteMeasure (μ i)) ∧
      Nonempty ((IntervalContinuous 𝕜 →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] lp (fun i => Lp 𝕜 1 (μ i)) 1) :=
  exists_continuousMapDual_bounded_measure_family 𝕜

end ThesisCommon
