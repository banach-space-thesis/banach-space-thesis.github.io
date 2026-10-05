import ThesisCommon.Analysis.L1EllOneFiniteInterference
import ThesisCommon.Analysis.AtomlessL1PrimaryFactorization
import ThesisCommon.Analysis.LpSemilinearIsometry
import ThesisCommon.Analysis.PrimaryIsomorphism
import ThesisCommon.Analysis.LpArbitraryProducts

/-! UPFP of the actual arbitrary-index ell1 sum of Lebesgue L1 spaces.
Uncountable indices use finite interference and Hajnal's theorem. Countable
nonempty indices are handled by an actual L1 isometry; the empty case is zero. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv

theorem intervalCantorEllOne_hasCPFP_eight (𝕜 Γ : Type*) [RCLike 𝕜]
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) :
    HasCPFP 𝕜 (EllOneSum Γ (Lp 𝕜 1 intervalCantorMeasure)) 8 := by
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace
  have hμ : intervalCantorMeasure ≠ 0 := MeasureTheory.IsProbabilityMeasure.ne_zero _
  have hr : HasCPFP ℝ (EllOneSum Γ (Lp ℝ 1 intervalCantorMeasure)) 8 := by
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using ellOne_hasCPFP_of_finite_interference hΓ
      (real_atomlessL1_hasEllOneFiniteInterference (I := Γ) hμ)
      (show (1 : ℝ) ≤ 4 by norm_num) (real_compactAtomlessL1_hasCPFP_four hμ)
  have hc : HasCPFP ℂ (EllOneSum Γ (Lp ℂ 1 intervalCantorMeasure)) 8 := by
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using ellOne_hasCPFP_of_finite_interference hΓ
      (complex_atomlessL1_hasEllOneFiniteInterference (I := Γ) hμ)
      (show (1 : ℝ) ≤ 4 by norm_num) (complex_compactAtomlessL1_hasCPFP_four hμ)
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hreal | hcomplex
  · let e := RCLike.realRingEquiv hreal
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.realLinearIsometryEquiv hreal).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
      simpa only [RingEquiv.symm_symm] using
        (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
    exact hr.of_semilinearIsometry e.symm
      (lpSemilinearIsometryEquiv (ι := Γ) e 1
        (measureLpScalarIsometryEquiv e intervalCantorMeasure 1)).symm
  · let e := RCLike.complexRingEquiv hcomplex
    letI : RingHomIsometric (RingHomClass.toRingHom e) :=
      ⟨fun {x} => (RCLike.complexLinearIsometryEquiv hcomplex).norm_map x⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm) := ⟨by
      intro x
      have h := scalarRingEquiv_norm e (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm⟩
    letI : RingHomIsometric (RingHomClass.toRingHom e.symm.symm) := by
      simpa only [RingEquiv.symm_symm] using
        (inferInstance : RingHomIsometric (RingHomClass.toRingHom e))
    exact hc.of_semilinearIsometry e.symm
      (lpSemilinearIsometryEquiv (ι := Γ) e 1
        (measureLpScalarIsometryEquiv e intervalCantorMeasure 1)).symm

def countableNonemptyProductNatEquiv (Γ : Type*) [Countable Γ] [Nonempty Γ] : Γ × ℕ ≃ ℕ := by
  apply Classical.choice
  apply Cardinal.lift_mk_eq'.mp
  simp only [Cardinal.lift_uzero, Cardinal.mk_eq_aleph0, Cardinal.mk_nat, Cardinal.lift_aleph0]

def intervalL1CountableEllOneEquiv (𝕜 Γ : Type*) [RCLike 𝕜] [Countable Γ] [Nonempty Γ] :
    EllOneSum Γ (IntervalLp 𝕜 ⟨1, le_rfl⟩) ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
  (lebesgueLpCoordinateEquiv (𝕜 := 𝕜) (p := 1) (by norm_num)
    (fun _ : Γ => intervalLpFunctionSelfSimilarity 𝕜 ⟨1, le_rfl⟩ (by simp))).trans
    ((lpProductFlattenIsometry (𝕜 := 𝕜) 1 (by norm_num) (countableNonemptyProductNatEquiv Γ)).trans
      (intervalLpFunctionSelfSimilarity 𝕜 ⟨1, le_rfl⟩ (by simp)).symm)

theorem intervalL1ArbitraryEllOne_hasUPFP (𝕜 Γ : Type*) [RCLike 𝕜] :
    HasUPFP 𝕜 (EllOneSum Γ (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := by
  classical
  by_cases hΓ : Cardinal.aleph0 < Cardinal.mk Γ
  · let e := lebesgueLpCoordinateEquiv (𝕜 := 𝕜) (p := 1) (by norm_num)
      (fun _ : Γ => intervalCantorL1Equiv 𝕜)
    exact (show HasUPFP 𝕜 (EllOneSum Γ (Lp 𝕜 1 intervalCantorMeasure)) from
      ⟨8, by norm_num, intervalCantorEllOne_hasCPFP_eight 𝕜 Γ hΓ⟩).of_equiv e.toContinuousLinearEquiv
  · letI : Countable Γ := Cardinal.mk_le_aleph0_iff.mp (le_of_not_gt hΓ)
    cases isEmpty_or_nonempty Γ with
    | inl hempty =>
      letI := hempty
      exact hasUPFP_of_subsingleton
    | inr hnonempty =>
      letI := hnonempty
      exact (intervalL1_hasUPFP 𝕜).of_equiv (intervalL1CountableEllOneEquiv 𝕜 Γ).symm.toContinuousLinearEquiv

end ThesisCommon
