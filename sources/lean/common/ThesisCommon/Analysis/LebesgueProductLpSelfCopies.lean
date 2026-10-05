import ThesisCommon.Analysis.InfiniteProductCoordinateSplit
import ThesisCommon.Analysis.ProductIntervalLpSelfCopies
import ThesisCommon.Analysis.EllOneFamilyTranspose
import Mathlib.Logic.Equiv.Option

/-! Self-similarity of genuine arbitrary-index products of restricted
Lebesgue probability measures. A coordinate is split by finite-cylinder
uniqueness, then its dyadic intervals provide the countable copies.
No homogeneity or measure-algebra classification theorem is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
instance lebesgueProduct_intervalProbability :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

variable {𝕜 Γ : Type*} [RCLike 𝕜] [Nonempty Γ]

def lebesgueProductLpSelfSimilarity (p : BanachExponent) (hp : p.val ≠ ∞) :
    Lp 𝕜 p.val (Measure.infinitePi fun _ : Γ => volume.restrict (Icc (0 : ℝ) 1)) ≃ₗᵢ[𝕜]
      lp (fun _ : ℕ => Lp 𝕜 p.val
        (Measure.infinitePi fun _ : Γ => volume.restrict (Icc (0 : ℝ) 1))) p.val := by
  classical
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  let i₀ : Γ := Classical.choice inferInstance
  let q := Equiv.optionSubtypeNe i₀
  let a := lebesgueLpTransport (𝕜 := 𝕜) (E := 𝕜) (p := p.val)
    (MeasurableEquiv.piCongrLeft (fun _ : Γ => ℝ) q)
    (show MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Γ => ℝ) q)
      (Measure.infinitePi fun _ : Option {j : Γ // j ≠ i₀} => ν)
      (Measure.infinitePi fun _ : Γ => ν) from
      ⟨(MeasurableEquiv.piCongrLeft _ q).measurable,
        Measure.infinitePi_map_piCongrLeft (fun _ : Γ => ν) q⟩)
  let b := infinitePiOptionLpEquiv (𝕜 := 𝕜)
    (fun _ : Option {j : Γ // j ≠ i₀} => ν) p.val
  let d := a.trans b
  let c := productIntervalLpSelfSimilarity (𝕜 := 𝕜)
    (Measure.infinitePi fun _ : {j : Γ // j ≠ i₀} => ν) p hp
  exact (d.trans c).trans
    (lebesgueLpCoordinateEquiv
      (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one p.property)) hp)
      (fun _ : ℕ => d.symm))

theorem exists_orthogonal_selfCopies_lebesgueProductLp
    (p : BanachExponent) (hp : p.val ≠ ∞) :
    ∃ J P : ℕ →
        Lp 𝕜 p.val (Measure.infinitePi fun _ : Γ => volume.restrict (Icc (0 : ℝ) 1)) →L[𝕜]
        Lp 𝕜 p.val (Measure.infinitePi fun _ : Γ => volume.restrict (Icc (0 : ℝ) 1)),
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) :=
  exists_orthogonal_selfCopies_of_sequence_equiv
    (lebesgueProductLpSelfSimilarity (𝕜 := 𝕜) (Γ := Γ) p hp).toContinuousLinearEquiv

/-- Arbitrary sums of the paper's Lebesgue-product models have actual
orthogonal complemented self-copies. Each product has at least one coordinate. -/
theorem exists_orthogonal_selfCopies_ellOne_lebesgueProducts
    {I : Type*} (κ : I → Type*) [∀ i, Nonempty (κ i)] :
    ∃ J P : ℕ →
        lp (fun i => Lp 𝕜 1 (Measure.infinitePi fun _ : κ i =>
          volume.restrict (Icc (0 : ℝ) 1))) 1 →L[𝕜]
        lp (fun i => Lp 𝕜 1 (Measure.infinitePi fun _ : κ i =>
          volume.restrict (Icc (0 : ℝ) 1))) 1,
      (∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ n m, n ≠ m → (P n).comp (J m) = 0) :=
  exists_orthogonal_selfCopies_ellOne_family
    (fun i => lebesgueProductLpSelfSimilarity (𝕜 := 𝕜) (Γ := κ i) ⟨1, le_rfl⟩ (by simp))

end ThesisCommon
