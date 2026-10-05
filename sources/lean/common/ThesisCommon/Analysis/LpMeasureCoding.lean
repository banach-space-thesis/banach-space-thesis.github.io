import ThesisCommon.Analysis.StandardMeasureRepresentation
import ThesisCommon.LpCut
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Lp isometries induced by measurable codings that generate the sigma algebra.
This realizes the L¹ isometry used after PEMS Theorem 3.7. The surjectivity proof
uses the checked measurable factorization theorem, whose proof constructs the
factor through simple functions and their limits. No pointwise inverse to the
coding is postulated. The cutoff identity is valid over both scalar fields. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable (μ : Measure X) (f : X → Y) (hf : Measurable f)

theorem lpComap_surjective (hgen : mY.comap f = mX) (p : ℝ≥0∞) :
    Function.Surjective (Lp.compMeasurePreserving f (⟨hf, rfl⟩ : MeasurePreserving f μ (μ.map f)) :
      Lp 𝕜 p (μ.map f) → Lp 𝕜 p μ) := by
  intro g
  have hg : StronglyMeasurable[mY.comap f] (fun x => g x) := by
    rw [hgen]
    exact Lp.stronglyMeasurable g
  obtain ⟨h, hh, heq⟩ := hg.exists_eq_measurable_comp
  have hLp : MemLp h p (μ.map f) := by
    apply (memLp_map_measure_iff hh.aestronglyMeasurable hf.aemeasurable).mpr
    rw [← heq]
    exact Lp.memLp g
  refine ⟨hLp.toLp h, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (hLp.toLp h)
      (⟨hf, rfl⟩ : MeasurePreserving f μ (μ.map f)),
    ae_of_ae_map hf.aemeasurable (MemLp.coeFn_toLp hLp)] with x hx hy
  exact hx.trans (hy.trans (congrFun heq x).symm)

/-- The genuine linear isometry equivalence induced by the coding, for all
1 ≤ p ≤ ∞ and either scalar field. -/
def lpComapEquiv (hgen : mY.comap f = mX) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p (μ.map f) ≃ₗᵢ[𝕜] Lp 𝕜 p μ :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ 𝕜 f (⟨hf, rfl⟩ : MeasurePreserving f μ (μ.map f)))
    (lpComap_surjective μ f hf hgen p)

theorem lpComapEquiv_coe (hgen : mY.comap f = mX) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : Lp 𝕜 p (μ.map f)) : lpComapEquiv μ f hf hgen p g =ᵐ[μ] g ∘ f :=
  Lp.coeFn_compMeasurePreserving g _

/-- Multiplication by a characteristic function is transported to the
characteristic function of its preimage, including for p=∞. -/
theorem lpComapEquiv_cut (hgen : mY.comap f = mX) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : Set Y) (hA : MeasurableSet A) (g : Lp 𝕜 p (μ.map f)) :
    lpComapEquiv μ f hf hgen p (lpCut A hA g) =
      lpCut (f ⁻¹' A) (hf hA) (lpComapEquiv μ f hf hgen p g) := by
  apply Lp.ext
  filter_upwards [lpComapEquiv_coe μ f hf hgen p (lpCut A hA g),
    lpComapEquiv_coe μ f hf hgen p g,
    lpCut_coe (f ⁻¹' A) (hf hA) (lpComapEquiv μ f hf hgen p g),
    ae_of_ae_map hf.aemeasurable (lpCut_coe A hA g)] with x hleft hg hright hcut
  by_cases hx : f x ∈ A <;> simp_all [Function.comp_apply]

/-- The actual L¹ equivalence associated to the standard Cantor model. -/
def cantorLOneEquiv (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] (μ : Measure X) [IsFiniteMeasure μ] :
    Lp 𝕜 1 (cantorMeasureModel X μ).measure ≃ₗᵢ[𝕜] Lp 𝕜 1 μ :=
  lpComapEquiv μ (MeasurableSpace.mapNatBool X) (MeasurableSpace.measurable_mapNatBool X)
    (comap_mapNatBool X) 1

end ThesisCommon
