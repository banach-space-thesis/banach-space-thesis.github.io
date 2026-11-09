import BanachIsometric.SignedSimplexBoundaryCount
import BanachIsometric.LipschitzConeBoundary
import BanachIsometric.LipschitzConeSupport

/-! The signed count is a cocycle on the actual Lipschitz chains. Therefore
coning two homologous cycles in a null shell gives the same count almost
everywhere, even when neither cycle comes from a single sphere map. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set MeasureTheory
open scoped Topology NNReal

theorem ae_rawSignedSimplexCount_boundary_zero (n : ℕ)
    (μ : Measure (Fin (n + 1) → ℝ)) [μ.IsAddHaarMeasure]
    (c : RawRationalChains (Fin (n + 1) → ℝ) (n + 2))
    (hc : c ∈ rawLipschitzCarrier (Fin (n + 1) → ℝ) (n + 2)) :
    ∀ᵐ y ∂μ, rawSignedSimplexCount (n + 1) (rawBoundary (n + 1) c) y = 0 := by
  let F := (rawSignedSimplexCount (n + 1)).comp (rawBoundary (n + 1))
  let Z : Submodule ℚ (RawRationalChains (Fin (n + 1) → ℝ) (n + 2)) :=
    { carrier := {c | ∀ᵐ y ∂μ, F c y = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change (∀ᵐ y ∂μ, F a y = 0) at ha
        change (∀ᵐ y ∂μ, F b y = 0) at hb
        change ∀ᵐ y ∂μ, F (a + b) y = 0
        filter_upwards [ha, hb] with y hay hby
        simp [hay, hby]
      smul_mem' := by
        intro a b hb
        change (∀ᵐ y ∂μ, F b y = 0) at hb
        change ∀ᵐ y ∂μ, F (a • b) y = 0
        filter_upwards [hb] with y hy
        simp [hy] }
  have hsub : rawLipschitzCarrier (Fin (n + 1) → ℝ) (n + 2) ≤ Z := by
    rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, ⟨L, hL⟩, rfl⟩
    exact ae_signedSimplexBoundaryCount_zero n μ σ hL
  exact hsub hc

theorem rawSignedSimplexCount_pushforward_zero_off_image {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) (f : C(X, Fin n → ℝ)) {L : ℝ≥0} (hL : LipschitzWith L f)
    (c : RawRationalChains X n) (hc : c ∈ rawLipschitzCarrier X n) {y : Fin n → ℝ}
    (hy : y ∉ range f) : rawSignedSimplexCount n (rawChainMap f n c) y = 0 := by
  let F := (LinearMap.proj (R := ℚ) y).comp ((rawSignedSimplexCount n).comp (rawChainMap f n))
  have hsub : rawLipschitzCarrier X n ≤ LinearMap.ker F := by
    rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, ⟨K, hK⟩, rfl⟩
    change rawSignedSimplexCount n (rawChainMap f n (Finsupp.single σ 1)) y = 0
    rw [show rawChainMap f n (Finsupp.single σ 1) = Finsupp.single (f.comp σ) 1 from by
      simp [rawChainMap], rawSignedSimplexCount_single, one_smul]
    apply signedSimplexCount_eq_zero_off_range n (f.comp σ) ⟨L * K, hL.comp hK⟩
    rintro ⟨x, rfl⟩
    exact hy ⟨σ x, rfl⟩
  exact LinearMap.mem_ker.mp (hsub hc)

theorem ae_rawSignedSimplexCount_cones_eq_of_shell_filling {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) (μ : Measure (Fin (n + 2) → ℝ)) [μ.IsAddHaarMeasure]
    (f : C(X, Fin (n + 2) → ℝ)) {L : ℝ≥0} (hL : LipschitzWith L f) (hf : μ (range f) = 0)
    (a b : RawRationalChains (Fin (n + 2) → ℝ) (n + 1))
    (z : RawRationalChains X (n + 2)) (hz : z ∈ rawLipschitzCarrier X (n + 2))
    (hfill : rawBoundary (n + 1) (rawChainMap f (n + 2) z) = a - b) :
    ∀ᵐ y ∂μ, rawSignedSimplexCount (n + 2) (rawLipschitzCone (n + 1) a) y =
      rawSignedSimplexCount (n + 2) (rawLipschitzCone (n + 1) b) y := by
  let w := rawChainMap f (n + 2) z
  have hw : w ∈ rawLipschitzCarrier (Fin (n + 2) → ℝ) (n + 2) :=
    rawChainMap_preserves_lipschitz f hL (n + 2) hz
  have hcone := rawBoundary_rawLipschitzCone (n + 1) w hw
  have hvan := ae_rawSignedSimplexCount_boundary_zero (n + 1) μ _
    (rawLipschitzCone_preserves_lipschitz (n + 2) hw)
  have hoff : ∀ᵐ y ∂μ, y ∉ range f := by rw [ae_iff]; simpa only [not_not] using hf
  filter_upwards [hvan, hoff] with y hy hyoff
  have hwzero := rawSignedSimplexCount_pushforward_zero_off_image (n + 2) f hL z hz hyoff
  change rawBoundary (n + 1) w = a - b at hfill
  simp only [hcone, hfill, map_sub, Pi.sub_apply] at hy
  change rawSignedSimplexCount (n + 2) w y = 0 at hwzero
  linarith

end BanachIsometric.SingularPrism
