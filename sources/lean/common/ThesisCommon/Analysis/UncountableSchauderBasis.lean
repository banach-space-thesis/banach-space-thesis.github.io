import ThesisCommon.Analysis.SchauderBasis
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Normalized unconditional expansions with an arbitrary index type.
The expansion is the genuine net over finite subsets, not an enumeration.
No multiplier, vector-valued sum space, or factorisation conclusion is a field.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable (𝕜 Γ E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A normalized family whose actual coordinate expansion is unconditionally summable. -/
structure NormalizedSchauderFamily where
  vector : Γ → E
  coord : Γ → E →L[𝕜] 𝕜
  biorthogonal : ∀ i j, coord i (vector j) = if i = j then 1 else 0
  norm_vector : ∀ i, ‖vector i‖ = 1
  expansion : ∀ x : E, HasSum (fun i => coord i x • vector i) x

variable {𝕜 Γ E}
namespace NormalizedSchauderFamily
variable (b : NormalizedSchauderFamily 𝕜 Γ E)

/-- Finite unconditional domination, allowing arbitrary scalar phases. -/
def UnconditionalWith (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ (F : Finset Γ) (a c : Γ → 𝕜),
    (∀ i ∈ F, ‖a i‖ ≤ ‖c i‖) →
    ‖∑ i ∈ F, a i • b.vector i‖ ≤ K * ‖∑ i ∈ F, c i • b.vector i‖

def IsUnconditional : Prop := ∃ K : ℝ, b.UnconditionalWith K

def IsOneUnconditional : Prop := b.UnconditionalWith 1

/-- Symmetry is finite permutation invariance together with one-unconditionality. -/
def HasSymmetricNorm : Prop := b.IsOneUnconditional ∧
  ∀ (σ : Equiv.Perm Γ) (F : Finset Γ) (a : Γ → 𝕜),
    ‖∑ i ∈ F, a i • b.vector (σ i)‖ = ‖∑ i ∈ F, a i • b.vector i‖

/-- The usual finite lower ℓ₁ estimate; normalization supplies the upper estimate. -/
def EquivalentEllOne : Prop := ∃ c : ℝ, 0 < c ∧
  ∀ (F : Finset Γ) (a : Γ → 𝕜),
    c * ∑ i ∈ F, ‖a i‖ ≤ ‖∑ i ∈ F, a i • b.vector i‖

theorem expansion_tendsto (x : E) :
    Tendsto (fun F : Finset Γ => ∑ i ∈ F, b.coord i x • b.vector i)
      atTop (𝓝 x) := b.expansion x

theorem finite_sum_norm_le (F : Finset Γ) (a : Γ → 𝕜) :
    ‖∑ i ∈ F, a i • b.vector i‖ ≤ ∑ i ∈ F, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ F, ‖a i • b.vector i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, b.norm_vector, mul_one]

theorem coord_finite_sum (F : Finset Γ) (a : Γ → 𝕜) (i : Γ) :
    b.coord i (∑ j ∈ F, a j • b.vector j) = if i ∈ F then a i else 0 := by
  classical
  simp [map_sum, map_smul, b.biorthogonal, Finset.sum_ite_eq]

/-- Coordinates separate points by uniqueness of the unconditional sum. -/
theorem ext {x y : E} (h : ∀ i, b.coord i x = b.coord i y) : x = y := by
  apply (b.expansion x).unique
  simpa only [h] using b.expansion y

/-- Any genuinely summable coefficient series has exactly its prescribed coordinates. -/
theorem coord_of_hasSum (a : Γ → 𝕜) {x : E}
    (hx : HasSum (fun i => a i • b.vector i) x) (i : Γ) : b.coord i x = a i := by
  classical
  have ht := ((b.coord i).continuous.tendsto x).comp hx
  have ht' : Tendsto (fun F : Finset Γ => b.coord i (∑ j ∈ F, a j • b.vector j))
      atTop (𝓝 (a i)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset Γ)] with F hF
    have hi : i ∈ F := Finset.singleton_subset_iff.mp hF
    simp only [b.coord_finite_sum, if_pos hi]
  exact tendsto_nhds_unique ht ht'

theorem coord_le_norm (hb : b.IsOneUnconditional) (i : Γ) (x : E) :
    ‖b.coord i x‖ ≤ ‖x‖ := by
  classical
  apply ge_of_tendsto (b.expansion_tendsto x).norm
  filter_upwards [eventually_ge_atTop ({i} : Finset Γ)] with F hF
  have hi : i ∈ F := Finset.singleton_subset_iff.mp hF
  have hh := hb.2 F (Pi.single i (b.coord i x)) (fun j => b.coord j x)
    (by
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne hji])
  simpa [Pi.single_apply, Finset.sum_ite_eq', hi, norm_smul, b.norm_vector] using hh

theorem norm_coord_eq_one (hb : b.IsOneUnconditional) (i : Γ) : ‖b.coord i‖ = 1 := by
  apply le_antisymm
  · apply (b.coord i).opNorm_le_bound zero_le_one
    intro x
    simpa only [one_mul] using b.coord_le_norm hb i x
  · have hh := (b.coord i).le_opNorm (b.vector i)
    simpa [b.biorthogonal, b.norm_vector] using hh

theorem norm_le_of_coordinate_majorant (x : E) {c : Γ → ℝ} {C : ℝ}
    (hc : HasSum c C) (hxc : ∀ i, ‖b.coord i x‖ ≤ c i) : ‖x‖ ≤ C := by
  apply le_of_tendsto' (b.expansion_tendsto x).norm
  intro F
  calc
    _ ≤ ∑ i ∈ F, ‖b.coord i x‖ := b.finite_sum_norm_le _ _
    _ ≤ ∑ i ∈ F, c i := Finset.sum_le_sum (fun i _ => hxc i)
    _ ≤ C := hc.tsum_eq ▸ hc.summable.sum_le_tsum _
      (fun i _ => (norm_nonneg _).trans (hxc i))

end NormalizedSchauderFamily
end ThesisCommon
