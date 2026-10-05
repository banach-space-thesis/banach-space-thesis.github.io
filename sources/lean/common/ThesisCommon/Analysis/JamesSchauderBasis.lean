import ThesisCommon.Analysis.JamesInitialConvergence
import ThesisCommon.Analysis.SchauderBasis

/-! The actual coordinate vectors form an ordered Schauder basis of finite-p
James space. Normalization is by each vector's actual James norm; no
unconditional convergence property is asserted. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

def jamesUnit (n : ℕ) : JamesSequenceSpace 𝕜 p :=
  lpToJames (𝕜 := 𝕜) p hp (lp.single p.val n (1 : 𝕜))

@[simp] theorem jamesUnit_apply (n k : ℕ) :
    jamesUnit (𝕜 := 𝕜) p hp n k = if k = n then 1 else 0 := by
  simp [jamesUnit, lp.single_apply, Pi.single_apply]

theorem jamesUnit_ne_zero (n : ℕ) : jamesUnit (𝕜 := 𝕜) p hp n ≠ 0 := by
  intro h
  have hh := congrArg (fun x : JamesSequenceSpace 𝕜 p => x n) h
  simp at hh

theorem jamesUnit_norm_pos (n : ℕ) : 0 < ‖jamesUnit (𝕜 := 𝕜) p hp n‖ :=
  norm_pos_iff.mpr (jamesUnit_ne_zero p hp n)

theorem james_finite_units_apply (F : Finset ℕ) (a : ℕ → 𝕜) (k : ℕ) :
    (∑ n ∈ F, a n • jamesUnit p hp n) k = if k ∈ F then a k else 0 := by
  classical
  change JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) k
    (∑ n ∈ F, a n • jamesUnit p hp n) = _
  simp [map_sum, map_smul, JamesSequenceSpace.coordinate, jamesUnit_apply,
    Finset.sum_ite_eq]

theorem james_finite_units_eq_initial (N : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    ∑ n ∈ Finset.range (N + 1), x n • jamesUnit p hp n =
      JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) N x := by
  ext k
  rw [james_finite_units_apply, JamesSequenceSpace.initial_apply]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem james_finite_units_tendsto (x : JamesSequenceSpace 𝕜 p) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, x n • jamesUnit p hp n) atTop (𝓝 x) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [james_finite_units_eq_initial] using JamesSequenceSpace.initial_tendsto hp x

def jamesNormalizedVector (n : ℕ) : JamesSequenceSpace 𝕜 p :=
  (‖jamesUnit (𝕜 := 𝕜) p hp n‖ : 𝕜)⁻¹ • jamesUnit p hp n

def jamesNormalizedCoordinate (n : ℕ) : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜 :=
  (‖jamesUnit (𝕜 := 𝕜) p hp n‖ : 𝕜) • JamesSequenceSpace.coordinate n

theorem jamesNormalizedVector_norm (n : ℕ) :
    ‖jamesNormalizedVector (𝕜 := 𝕜) p hp n‖ = 1 := by
  rw [jamesNormalizedVector, norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_pos (jamesUnit_norm_pos p hp n), inv_mul_cancel₀ (jamesUnit_norm_pos p hp n).ne']

theorem jamesNormalized_biorthogonal (i j : ℕ) :
    jamesNormalizedCoordinate (𝕜 := 𝕜) p hp i (jamesNormalizedVector p hp j) =
      if i = j then 1 else 0 := by
  classical
  have hn : (‖jamesUnit (𝕜 := 𝕜) p hp j‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (jamesUnit_norm_pos p hp j).ne'
  by_cases hij : i = j
  · subst i
    simp [jamesNormalizedCoordinate, jamesNormalizedVector, hn,
      JamesSequenceSpace.coordinate]
  · simp [jamesNormalizedCoordinate, jamesNormalizedVector, hij,
      JamesSequenceSpace.coordinate]

theorem jamesNormalized_term (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    jamesNormalizedCoordinate (𝕜 := 𝕜) p hp n x •
      jamesNormalizedVector (𝕜 := 𝕜) p hp n =
      x n • jamesUnit (𝕜 := 𝕜) p hp n := by
  have hn : (‖jamesUnit (𝕜 := 𝕜) p hp n‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (jamesUnit_norm_pos p hp n).ne'
  change ((‖jamesUnit (𝕜 := 𝕜) p hp n‖ : 𝕜) * x n) •
    ((‖jamesUnit (𝕜 := 𝕜) p hp n‖ : 𝕜)⁻¹ • jamesUnit p hp n) = _
  rw [smul_smul]
  congr 1
  field_simp

/-- A normalized, ordered Schauder basis on the genuine Banach space Jp. -/
def jamesSchauderBasis : NormalizedSchauderBasis 𝕜 (JamesSequenceSpace 𝕜 p) where
  vector := jamesNormalizedVector p hp
  coord := jamesNormalizedCoordinate p hp
  biorthogonal := jamesNormalized_biorthogonal p hp
  norm_vector := jamesNormalizedVector_norm p hp
  expansion x := by
    simpa only [jamesNormalized_term] using james_finite_units_tendsto p hp x

end ThesisCommon
