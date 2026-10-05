import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-! The Riesz-Kantorovich positive-part construction for real bounded
functionals on C(K). This supplies the positive-functional decomposition
needed before applying mathlib's positive Riesz representation theorem. -/
noncomputable section
open scoped Pointwise
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem continuousMap_norm_le_of_nonneg_le {f g : C(K, ℝ)}
    (hg : 0 ≤ g) (hgf : g ≤ f) : ‖g‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ g t from hg t)]
  exact (hgf t).trans ((le_abs_self (f t)).trans (f.norm_coe_le_norm t))

def continuousMapPositiveValue (μ : C(K, ℝ) →L[ℝ] ℝ) (f : C(K, ℝ)) : ℝ :=
  sSup (μ '' Set.Icc 0 f)

theorem continuousMap_positive_image_nonempty (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) : (μ '' Set.Icc 0 f).Nonempty :=
  ⟨μ 0, Set.mem_image_of_mem μ ⟨le_rfl, hf⟩⟩

theorem continuousMap_positive_image_bddAbove (μ : C(K, ℝ) →L[ℝ] ℝ)
    (f : C(K, ℝ)) : BddAbove (μ '' Set.Icc 0 f) := by
  refine ⟨‖μ‖ * ‖f‖, ?_⟩
  rintro y ⟨g, hg, rfl⟩
  calc
    μ g ≤ ‖μ g‖ := le_abs_self _
    _ ≤ ‖μ‖ * ‖g‖ := μ.le_opNorm g
    _ ≤ ‖μ‖ * ‖f‖ := mul_le_mul_of_nonneg_left
      (continuousMap_norm_le_of_nonneg_le hg.1 hg.2) (norm_nonneg μ)

theorem continuousMapPositiveValue_nonneg (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) : 0 ≤ continuousMapPositiveValue μ f := by
  have h := le_csSup (continuousMap_positive_image_bddAbove μ f)
    (Set.mem_image_of_mem μ (show (0 : C(K, ℝ)) ∈ Set.Icc 0 f from ⟨le_rfl, hf⟩))
  simpa only [map_zero] using h

theorem continuousMapPositiveValue_le (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) : continuousMapPositiveValue μ f ≤ ‖μ‖ * ‖f‖ := by
  apply csSup_le (continuousMap_positive_image_nonempty μ hf)
  rintro y ⟨g, hg, rfl⟩
  exact (le_abs_self (μ g)).trans ((μ.le_opNorm g).trans
    (mul_le_mul_of_nonneg_left (continuousMap_norm_le_of_nonneg_le hg.1 hg.2) (norm_nonneg μ)))

theorem le_continuousMapPositiveValue (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f : C(K, ℝ)} (hf : 0 ≤ f) : μ f ≤ continuousMapPositiveValue μ f :=
  le_csSup (continuousMap_positive_image_bddAbove μ f) (Set.mem_image_of_mem μ ⟨hf, le_rfl⟩)

theorem continuousMap_positive_image_add (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f g : C(K, ℝ)} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    μ '' Set.Icc 0 (f+g) = (μ '' Set.Icc 0 f) + (μ '' Set.Icc 0 g) := by
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    let u : C(K, ℝ) := h ⊓ f
    let v : C(K, ℝ) := h - u
    have hu : u ∈ Set.Icc 0 f := ⟨le_inf hh.1 hf, inf_le_right⟩
    have hv : v ∈ Set.Icc 0 g := by
      constructor
      · exact sub_nonneg.2 inf_le_left
      · intro t
        change h t - min (h t) (f t) ≤ g t
        rcases le_total (h t) (f t) with htf | hft
        · rw [min_eq_left htf, sub_self]
          exact hg t
        · rw [min_eq_right hft]
          have ht := hh.2 t
          change h t ≤ f t + g t at ht
          linarith
    refine Set.mem_add.2 ⟨μ u, Set.mem_image_of_mem μ hu, μ v, Set.mem_image_of_mem μ hv, ?_⟩
    rw [← map_add]
    congr 1
    dsimp [v]
    abel
  · rintro ⟨a, ⟨u, hu, rfl⟩, b, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u+v, ⟨add_nonneg hu.1 hv.1, add_le_add hu.2 hv.2⟩, map_add μ u v⟩

theorem continuousMapPositiveValue_add (μ : C(K, ℝ) →L[ℝ] ℝ)
    {f g : C(K, ℝ)} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    continuousMapPositiveValue μ (f+g) =
      continuousMapPositiveValue μ f + continuousMapPositiveValue μ g := by
  unfold continuousMapPositiveValue
  rw [continuousMap_positive_image_add μ hf hg]
  exact csSup_add (continuousMap_positive_image_nonempty μ hf)
    (continuousMap_positive_image_bddAbove μ f) (continuousMap_positive_image_nonempty μ hg)
    (continuousMap_positive_image_bddAbove μ g)

end ThesisCommon
