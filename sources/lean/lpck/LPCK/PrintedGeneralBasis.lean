import LPCK.PrintedUpperTriangular

/-! Unnormalized one-unconditional bases and their actual vector sums.
Storage in normalized coordinates is an isometric change of coordinates,
not a hypothesis on the norms of the printed basis vectors. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace LPCK.Printed
open ThesisCommon
set_option synthInstance.maxHeartbeats 150000
set_option maxHeartbeats 1200000

variable {𝕜 E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

structure OneUnconditionalBasis (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] where
  vector : ℕ → E
  coord : ℕ → E →L[𝕜] 𝕜
  biorthogonal : ∀ i j, coord i (vector j) = if i = j then 1 else 0
  expansion : ∀ x : E, Tendsto (fun N => ∑ i ∈ Finset.range N, coord i x • vector i)
    atTop (𝓝 x)
  domination : ∀ (F : Finset ℕ) (a c : ℕ → 𝕜),
    (∀ i ∈ F, ‖a i‖ ≤ ‖c i‖) →
    ‖∑ i ∈ F, a i • vector i‖ ≤ ‖∑ i ∈ F, c i • vector i‖

namespace OneUnconditionalBasis
variable (b : OneUnconditionalBasis 𝕜 E)

def weight (n : ℕ) : 𝕜 := (‖b.vector n‖ : ℝ)

theorem weight_norm (n : ℕ) : ‖b.weight n‖ = ‖b.vector n‖ := by
  simp only [weight, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

theorem weight_ne_zero (n : ℕ) : b.weight n ≠ 0 := by
  apply norm_pos_iff.mp
  rw [b.weight_norm]
  apply norm_pos_iff.mpr
  intro h
  have hc := b.biorthogonal n n
  simp [h] at hc

def normalize : NormalizedSchauderBasis 𝕜 E where
  vector n := (b.weight n)⁻¹ • b.vector n
  coord n := b.weight n • b.coord n
  biorthogonal i j := by
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, b.biorthogonal]
    split_ifs with h
    · subst j
      rw [mul_one, inv_mul_cancel₀ (b.weight_ne_zero i)]
    · simp
  norm_vector n := by
    rw [norm_smul, norm_inv, b.weight_norm, inv_mul_cancel₀ (by
      rw [← b.weight_norm n]; exact norm_ne_zero_iff.mpr (b.weight_ne_zero n))]
  expansion x := by
    have h (n : ℕ) : (b.weight n * b.coord n x) • ((b.weight n)⁻¹ • b.vector n) =
        b.coord n x • b.vector n := by
      rw [smul_smul, mul_comm (b.weight n), mul_assoc, mul_inv_cancel₀ (b.weight_ne_zero n), mul_one]
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, h] using b.expansion x

theorem normalize_unconditional : b.normalize.IsOneUnconditional := by
  refine ⟨le_rfl, ?_⟩
  intro F a c h
  simpa only [normalize, smul_smul, one_mul] using
    b.domination F (fun i => a i * (b.weight i)⁻¹) (fun i => c i * (b.weight i)⁻¹)
      (fun i hi => by
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_right (h i hi) (norm_nonneg _))

variable [CompleteSpace E]

/-- An element stores `‖eₙ‖ • xₙ` in coordinate n. -/
abbrev Sum (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  SchauderSum b.normalize b.normalize_unconditional X

def rawCoordinate (x : b.Sum X) (i : ℕ) : X := (b.weight i)⁻¹ • x i

private theorem normalized_term (i : ℕ) (x : X) :
    (‖(b.weight i)⁻¹ • x‖ : 𝕜) • b.vector i =
      (‖x‖ : 𝕜) • b.normalize.vector i := by
  rw [norm_smul, norm_inv, b.weight_norm, RCLike.ofReal_mul, RCLike.ofReal_inv]
  change ((↑‖b.vector i‖ : 𝕜)⁻¹ * (‖x‖ : 𝕜)) • b.vector i =
    (‖x‖ : 𝕜) • ((↑‖b.vector i‖ : 𝕜)⁻¹ • b.vector i)
  rw [smul_smul, mul_comm]

/-- The stored norm is the norm of the series in the author's basis. -/
theorem raw_norm_series (x : b.Sum X) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, (‖b.rawCoordinate x i‖ : 𝕜) • b.vector i)
      atTop (𝓝 (SchauderSum.normVector x)) := by
  simpa only [rawCoordinate, b.normalized_term] using SchauderSum.normVector_expansion x

/-- Every sequence in the printed sum has a stored representative. -/
theorem exists_stored (x : ℕ → X) (v : E)
    (hx : Tendsto (fun N => ∑ i ∈ Finset.range N, (‖x i‖ : 𝕜) • b.vector i) atTop (𝓝 v)) :
    ∃ y : b.Sum X, (∀ i, b.rawCoordinate y i = x i) ∧ ‖y‖ = ‖v‖ := by
  let z (i : ℕ) := b.weight i • x i
  have hz (i : ℕ) : (b.weight i)⁻¹ • z i = x i := by
    dsimp [z]
    rw [smul_smul, inv_mul_cancel₀ (b.weight_ne_zero i), one_smul]
  have hv (i : ℕ) : b.normalize.coord i v = (‖z i‖ : 𝕜) := by
    apply tendsto_nhds_unique ((b.normalize.coord i).continuous.tendsto v |>.comp hx)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with N hN
    change (‖z i‖ : 𝕜) = b.normalize.coord i (∑ j ∈ Finset.range N,
      (‖x j‖ : 𝕜) • b.vector j)
    have hterm (j : ℕ) : (‖x j‖ : 𝕜) • b.vector j =
        (‖z j‖ : 𝕜) • b.normalize.vector j := by
      rw [← hz j]
      exact b.normalized_term j (z j)
    simp only [hterm]
    rw [b.normalize.coord_finite_sum]
    simp [hN]
  let y : b.Sum X := ⟨z, ⟨v, hv⟩⟩
  refine ⟨y, hz, ?_⟩
  rw [SchauderSum.norm_def, SchauderSum.normVector_eq y v hv]

end OneUnconditionalBasis

variable [CompleteSpace E] [CompleteSpace X]

/-- LPCK Proposition 3.5 for arbitrary basis-vector norms, expressed in
the actual supported space and the original, unscaled matrix coordinates. -/
theorem proposition_3_5_general (b : OneUnconditionalBasis 𝕜 E)
    (hcompact : ∀ S : X →L[𝕜] E, IsCompactOperator S)
    (T : b.Sum X →L[𝕜] b.Sum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℕ ↪ ℕ) (U : schauderSupported (b := b.normalize) (hb := b.normalize_unconditional)
        (X := X) (Set.range f) →L[𝕜] schauderSupported (b := b.normalize)
          (hb := b.normalize_unconditional) (X := X) (Set.range f)),
      StrictMono f ∧
      ‖((schauderProject (Set.range f)).comp T).comp
        (schauderSupported (Set.range f)).subtypeL - U‖ < ε ∧
      ∀ i j (x : X), b.rawCoordinate
        (U (schauderSupportedSingle (Set.mem_range_self j) (b.weight (f j) • x))).val (f i) =
        if i ≤ j then b.rawCoordinate
          (T (SchauderSum.single (f j) (b.weight (f j) • x))) (f i) else 0 := by
  obtain ⟨f, U, hf, hn, h⟩ := proposition_3_5 hcompact T hε
  refine ⟨f, U, hf, hn, ?_⟩
  intro i j x
  dsimp only [OneUnconditionalBasis.rawCoordinate]
  rw [h]
  split_ifs
  · rfl
  · exact smul_zero _

end LPCK.Printed
