import ThesisCommon.Analysis.UncountableSchauderSumComplete

/-! Correspondence with the manuscript's series definition, exact finite
coordinate norms, and convergence of coordinate truncations in X(Y).
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y]

/-- Equivalence with the original series membership condition. This
establishes both directions of the representation used for X(Y). -/
theorem memUncountableSchauderSum_iff_convergent (b : NormalizedSchauderFamily 𝕜 Γ X) (y : Γ → Y) :
    MemUncountableSchauderSum b y ↔ ∃ x : X,
      Tendsto (fun F : Finset Γ => ∑ n ∈ F, (‖y n‖ : 𝕜) • b.vector n) atTop (𝓝 x) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa only [hx] using b.expansion_tendsto x⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i
    have ht := ((b.coord i).continuous.tendsto x).comp hx
    apply tendsto_nhds_unique ht
    have he : (fun F : Finset Γ => b.coord i (∑ n ∈ F,
        (‖y n‖ : 𝕜) • b.vector n)) =ᶠ[atTop] (fun _ => (‖y i‖ : 𝕜)) := by
      filter_upwards [eventually_ge_atTop ({i} : Finset Γ)] with F hF
      rw [b.coord_finite_sum, if_pos (Finset.mem_of_subset hF (Finset.mem_singleton_self i))]
    exact tendsto_const_nhds.congr' he.symm

namespace UncountableSchauderSum
variable [CompleteSpace X] [NormedSpace 𝕜 Y]
variable {b : NormalizedSchauderFamily 𝕜 Γ X} {hb : b.IsOneUnconditional}

/-- A one-coordinate vector in the actual basis sum. -/
def single (n : Γ) (y : Y) : UncountableSchauderSum b hb Y :=
  ⟨Pi.single n y, (‖y‖ : 𝕜) • b.vector n, by
    intro i
    by_cases hi : i = n
    · subst i; simp [b.biorthogonal]
    · simp [b.biorthogonal, hi]⟩

@[simp] theorem single_apply (n : Γ) (y : Y) (i : Γ) :
    (single (b := b) (hb := hb) n y) i = if i = n then y else 0 := by
  classical
  change (Pi.single n y : Γ → Y) i = _
  exact Pi.single_apply n y i

@[simp] theorem sum_apply {ι : Type*} (F : Finset ι) (f : ι → UncountableSchauderSum b hb Y) (n : Γ) :
    (∑ i ∈ F, f i) n = ∑ i ∈ F, f i n :=
  map_sum (coordinate (b := b) (hb := hb) (Y := Y) n) f F

/-- The norm-vector of a finite coordinate sum is exactly its finite scalar
norm sum in X, rather than merely a bound for it. -/
theorem normVector_sum_single (F : Finset Γ) (y : Γ → Y) :
    normVector (∑ n ∈ F, single (b := b) (hb := hb) n (y n)) =
      ∑ n ∈ F, (‖y n‖ : 𝕜) • b.vector n := by
  classical
  apply normVector_eq
  intro i
  rw [b.coord_finite_sum, sum_apply]
  simp only [single_apply, Finset.sum_ite_eq]
  by_cases hi : i ∈ F <;> simp [hi]

theorem norm_sum_single (F : Finset Γ) (y : Γ → Y) :
    ‖∑ n ∈ F, single (b := b) (hb := hb) n (y n)‖ =
      ‖∑ n ∈ F, (‖y n‖ : 𝕜) • b.vector n‖ := by
  rw [norm_def, normVector_sum_single]

@[simp] theorem norm_single (n : Γ) (y : Y) :
    ‖single (b := b) (hb := hb) n y‖ = ‖y‖ := by
  have h := norm_sum_single (b := b) (hb := hb) {n} (fun _ => y)
  simpa [norm_smul, RCLike.norm_ofReal, b.norm_vector] using h

theorem normVector_sub_sum_single (y : UncountableSchauderSum b hb Y) (F : Finset Γ) :
    normVector (y - ∑ n ∈ F, single n (y n)) =
      normVector y - ∑ n ∈ F, (‖y n‖ : 𝕜) • b.vector n := by
  classical
  apply normVector_eq
  intro i
  rw [map_sub, coord_normVector, b.coord_finite_sum, sub_apply, sum_apply]
  simp only [single_apply, Finset.sum_ite_eq]
  by_cases hi : i ∈ F <;> simp [hi]

/-- Finite coordinate truncations converge in the sum norm. -/
theorem expansion (y : UncountableSchauderSum b hb Y) :
    Tendsto (fun F : Finset Γ => ∑ n ∈ F, single n (y n)) atTop (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := ((normVector_expansion y).sub (tendsto_const_nhds (x := normVector y))).norm
  simp only [sub_self, norm_zero] at ht
  convert ht using 1
  funext F
  rw [norm_sub_rev, norm_def, normVector_sub_sum_single, norm_sub_rev]

end UncountableSchauderSum
end ThesisCommon

