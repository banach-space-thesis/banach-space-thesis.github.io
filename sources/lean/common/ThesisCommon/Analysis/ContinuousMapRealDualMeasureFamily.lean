import ThesisCommon.Analysis.ContinuousMapPrincipalL1Equiv
import ThesisCommon.Analysis.ALBandDecomposition
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity

/-! The real dual of C(K) is the ordered ell-one sum of L1 spaces of
actual finite Borel measures on K, obtained from a maximal disjoint family
of positive dual functionals and their Riesz measures. -/
noncomputable section
universe u
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]

set_option maxHeartbeats 1000000 in
theorem exists_ordered_continuousMapDual_measure_family :
    ∃ (I : Type u) (μ : I → Measure K), (∀ i, IsFiniteMeasure (μ i)) ∧
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
  refine ⟨S, μ, fun i => inferInstance, b.trans c, ?_⟩
  intro φ
  have hc (i : S) : 0 ≤ (b.trans c) φ i ↔ 0 ≤ b φ i := by
    change 0 ≤ (continuousMapPrincipalL1Equiv (a i) (ha i)).symm (b φ i) ↔ 0 ≤ b φ i
    have h := continuousMapPrincipalL1Equiv_nonneg_iff (a i) (ha i)
      ((continuousMapPrincipalL1Equiv (a i) (ha i)).symm (b φ i))
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  exact (alBandIsometryEquiv_nonneg_iff continuousMapDual_norm_add_of_nonneg a ha hd ht φ).trans
    (forall_congr' fun i => (hc i).symm)

end ThesisCommon
