import ThesisCommon.Analysis.SchauderOperators

/-! Removing the first vector gives a genuine Schauder basis of the kernel
of its first coefficient. Uniform prefix bounds give uniform coordinate
bounds without an unconditionality assumption. -/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : NormalizedSchauderBasis 𝕜 X)

abbrev KernelTailSpace := LinearMap.ker (b.coord 0).toLinearMap

def kernelTail : NormalizedSchauderBasis 𝕜 b.KernelTailSpace where
  vector n := ⟨b.vector (n + 1), by
    change b.coord 0 (b.vector (n + 1)) = 0
    rw [b.biorthogonal, if_neg (by omega)]⟩
  coord n := (b.coord (n + 1)).comp (LinearMap.ker (b.coord 0).toLinearMap).subtypeL
  biorthogonal i j := by
    change b.coord (i + 1) (b.vector (j + 1)) = if i = j then 1 else 0
    rw [b.biorthogonal]
    simp
  norm_vector n := b.norm_vector (n + 1)
  expansion x := by
    apply tendsto_subtype_rng.mpr
    have hx : b.coord 0 x.val = 0 := x.property
    have h := (b.expansion x.val).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext N
    simp [Function.comp_apply, Finset.sum_range_succ', hx]

theorem kernelTail_prefix_norm_le {K : ℝ}
    (hK : ∀ N x, ‖∑ i ∈ Finset.range N, b.coord i x • b.vector i‖ ≤ K * ‖x‖)
    (N : ℕ) (x : b.KernelTailSpace) :
    ‖∑ i ∈ Finset.range N, b.kernelTail.coord i x • b.kernelTail.vector i‖ ≤ K * ‖x‖ := by
  have hx : b.coord 0 x.val = 0 := x.property
  have hh := hK (N + 1) x.val
  rw [Finset.sum_range_succ', hx, zero_smul, add_zero] at hh
  have heq :
      ((∑ i ∈ Finset.range N, b.kernelTail.coord i x • b.kernelTail.vector i :
        b.KernelTailSpace) : X) =
      ∑ i ∈ Finset.range N, b.coord (i + 1) x.val • b.vector (i + 1) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  change ‖((∑ i ∈ Finset.range N, b.kernelTail.coord i x • b.kernelTail.vector i :
    b.KernelTailSpace) : X)‖ ≤ K * ‖x.val‖
  rw [heq]
  exact hh

theorem coord_norm_le_of_prefix_bound {K : ℝ} (hK : 0 ≤ K)
    (hp : ∀ N x, ‖∑ i ∈ Finset.range N, b.coord i x • b.vector i‖ ≤ K * ‖x‖)
    (i : ℕ) : ‖b.coord i‖ ≤ 2 * K := by
  apply (b.coord i).opNorm_le_bound (by positivity)
  intro x
  have hterm : b.coord i x • b.vector i =
      (∑ j ∈ Finset.range (i + 1), b.coord j x • b.vector j) -
        (∑ j ∈ Finset.range i, b.coord j x • b.vector j) := by
    rw [Finset.sum_range_succ]
    abel
  calc
    ‖b.coord i x‖ = ‖b.coord i x • b.vector i‖ := by
      rw [norm_smul, b.norm_vector, mul_one]
    _ = _ := congrArg norm hterm
    _ ≤ ‖∑ j ∈ Finset.range (i + 1), b.coord j x • b.vector j‖ +
        ‖∑ j ∈ Finset.range i, b.coord j x • b.vector j‖ := norm_sub_le _ _
    _ ≤ K * ‖x‖ + K * ‖x‖ := add_le_add (hp _ _) (hp _ _)
    _ = (2 * K) * ‖x‖ := by ring

end ThesisCommon.NormalizedSchauderBasis
