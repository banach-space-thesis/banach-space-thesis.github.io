import BanachIsometric.SignedSimplexNullBoundary
import BanachIsometric.RawLipschitzChains
import BanachIsometric.LipschitzSignedArea
import BanachIsometric.SignedCountExcision

/-! The signed count of a real singular simplex is the actual oriented
fiber count in its affine coordinates. The Lipschitz extension is used for
the ordinary derivative. At almost every target all preimages are regular
and in the interior, where the derivative depends only on the simplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set MeasureTheory
open scoped Topology NNReal

theorem exists_signedSimplexExtension (n : ℕ)
    (σ : RawSingularSimplex (Fin n → ℝ) n) {L : ℝ≥0} (hL : LipschitzWith L σ) :
    ∃ f : (Fin n → ℝ) → (Fin n → ℝ),
      (∃ K : ℝ≥0, LipschitzWith K f) ∧
      ∀ x : signedSimplexDomain n, f x.val = σ ((signedSimplexCoordinates n).symm x) := by
  classical
  let f : signedSimplexDomain n → (Fin n → ℝ) := σ ∘ (signedSimplexCoordinates n).symm
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => if hx : x ∈ signedSimplexDomain n then f ⟨x, hx⟩ else 0
  have hg : LipschitzOnWith (L * ((n : ℝ≥0) + 1)) g (signedSimplexDomain n) := by
    apply lipschitzOnWith_iff_restrict.mpr
    have heq : (signedSimplexDomain n).restrict g = f := by
      funext x
      simp only [Set.restrict_apply, g, dif_pos x.property]
    rw [heq]
    exact hL.comp (signedSimplexCoordinates_symm_lipschitz n)
  obtain ⟨F, hF, hEq⟩ := hg.extend_pi
  refine ⟨F, ⟨_, hF⟩, ?_⟩
  intro x
  simpa only [g, dif_pos x.property, f, Function.comp_apply] using (hEq x.property).symm

def signedSimplexExtension (n : ℕ) (σ : RawSingularSimplex (Fin n → ℝ) n) :
    (Fin n → ℝ) → (Fin n → ℝ) := by
  classical
  exact if h : ∃ L : ℝ≥0, LipschitzWith L σ then
    Classical.choose (exists_signedSimplexExtension n σ (Classical.choose_spec h)) else 0

theorem signedSimplexExtension_spec (n : ℕ) (σ : RawSingularSimplex (Fin n → ℝ) n)
    (h : ∃ L : ℝ≥0, LipschitzWith L σ) :
    (∃ K : ℝ≥0, LipschitzWith K (signedSimplexExtension n σ)) ∧
      ∀ x : signedSimplexDomain n,
        signedSimplexExtension n σ x.val = σ ((signedSimplexCoordinates n).symm x) := by
  rw [signedSimplexExtension, dif_pos h]
  exact Classical.choose_spec (exists_signedSimplexExtension n σ (Classical.choose_spec h))

def signedSimplexCount (n : ℕ) (σ : RawSingularSimplex (Fin n → ℝ) n) : (Fin n → ℝ) → ℝ :=
  fun y => (signedFiberCount (signedSimplexExtension n σ) (fderiv ℝ (signedSimplexExtension n σ))
    (signedSimplexDomain n) y : ℝ)

def rawSignedSimplexCount (n : ℕ) :
    RawRationalChains (Fin n → ℝ) n →ₗ[ℚ] ((Fin n → ℝ) → ℝ) :=
  Finsupp.linearCombination ℚ (signedSimplexCount n)

@[simp] theorem rawSignedSimplexCount_single (n : ℕ)
    (σ : RawSingularSimplex (Fin n → ℝ) n) (a : ℚ) :
    rawSignedSimplexCount n (Finsupp.single σ a) = a • signedSimplexCount n σ := by
  simp only [rawSignedSimplexCount, Finsupp.linearCombination_single]

theorem signedSimplexCount_eq_zero_off_range (n : ℕ) (σ : RawSingularSimplex (Fin n → ℝ) n)
    (h : ∃ L : ℝ≥0, LipschitzWith L σ) {y : Fin n → ℝ} (hy : y ∉ Set.range σ) :
    signedSimplexCount n σ y = 0 := by
  unfold signedSimplexCount
  rw [signedFiberCount_eq_zero_of_not_mem_image, Int.cast_zero]
  rintro ⟨x, hx, rfl⟩
  exact hy ⟨(signedSimplexCoordinates n).symm ⟨x, hx⟩, (signedSimplexExtension_spec n σ h).2 _ |>.symm⟩

theorem signedSimplexExtension_ae_regular_interior (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (σ : RawSingularSimplex (Fin n → ℝ) n) (h : ∃ L : ℝ≥0, LipschitzWith L σ) :
    ∀ᵐ y ∂μ, ∀ x ∈ signedSimplexDomain n, signedSimplexExtension n σ x = y →
      x ∈ interior (signedSimplexDomain n) ∧
      DifferentiableAt ℝ (signedSimplexExtension n σ) x ∧
      (fderiv ℝ (signedSimplexExtension n σ) x).det ≠ 0 := by
  obtain ⟨K, hK⟩ := (signedSimplexExtension_spec n σ h).1
  have hnull := lipschitzWith_sends_null_sets_to_null μ μ rfl hK
    (signedSimplexDomain n \ interior (signedSimplexDomain n))
    (measure_signedSimplexDomain_diff_interior n μ)
  have havoid : ∀ᵐ y ∂μ, y ∉ signedSimplexExtension n σ ''
      (signedSimplexDomain n \ interior (signedSimplexDomain n)) := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [havoid, lipschitzWith_ae_every_preimage_regular μ hK] with y hy hreg
  intro x hx hxy
  refine ⟨?_, hreg x hxy⟩
  by_contra hxi
  exact hy ⟨x, ⟨hx, hxi⟩, hxy⟩

theorem integral_signedSimplexCount (n : ℕ) [NeZero n]
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure]
    (σ : RawSingularSimplex (Fin n → ℝ) n) (h : ∃ L : ℝ≥0, LipschitzWith L σ)
    {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    (∫ y, signedSimplexCount n σ y * g y ∂μ) =
      ∫ x in signedSimplexDomain n,
        (fderiv ℝ (signedSimplexExtension n σ) x).det * g (signedSimplexExtension n σ x) ∂μ := by
  obtain ⟨K, hK⟩ := (signedSimplexExtension_spec n σ h).1
  exact integral_signedFiberCount_of_compact_lipschitz μ hK (isCompact_signedSimplexDomain n) hg

end BanachIsometric.SingularPrism
