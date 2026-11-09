import LindenstraussRetraction.BidualIsometry
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.Linarith

/-! # The continuous bidual of a maximum-norm product -/

noncomputable section

namespace LindenstraussRetraction

universe u v s

variable {𝕜 : Type s} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

private def normalizePhase (a : 𝕜) : 𝕜 := (‖a‖ : 𝕜) * a⁻¹

private theorem normalizePhase_mul (a : 𝕜) : normalizePhase a * a = (‖a‖ : 𝕜) := by
  by_cases ha : a = 0
  · simp [normalizePhase, ha]
  · simp [normalizePhase, ha]

private theorem norm_normalizePhase_le (a : 𝕜) : ‖normalizePhase a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [normalizePhase, ha]
  · simp [normalizePhase, norm_mul, norm_inv,
      norm_ne_zero_iff.mpr ha]

/-- Values on the two coordinate directions can be aligned in phase. -/
theorem dual_product_evaluation_sum_le (f : StrongDual 𝕜 (E × F))
    (x : E) (y : F) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖f (x, 0)‖ + ‖f (0, y)‖ ≤ ‖f‖ := by
  let a := normalizePhase (f (x, 0))
  let b := normalizePhase (f (0, y))
  have hx' : ‖a • x‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_mul (norm_normalizePhase_le _) hx (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hy' : ‖b • y‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_mul (norm_normalizePhase_le _) hy (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hvalue : f (a • x, b • y) = ((‖f (x, 0)‖ + ‖f (0, y)‖ : ℝ) : 𝕜) := by
    have hsplit : (a • x, b • y) = a • (x, (0 : F)) + b • ((0 : E), y) := by simp
    rw [hsplit, map_add, map_smul, map_smul]
    change a * f (x, 0) + b * f (0, y) = _
    rw [normalizePhase_mul, normalizePhase_mul, RCLike.ofReal_add]
  calc
    ‖f (x, 0)‖ + ‖f (0, y)‖ = ‖f (a • x, b • y)‖ := by
      rw [hvalue, RCLike.norm_ofReal, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ ‖f‖ * ‖(a • x, b • y)‖ := f.le_opNorm _
    _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left (max_le hx' hy') (norm_nonneg f)
    _ = ‖f‖ := mul_one _

theorem norm_dual_product_left_le (f : StrongDual 𝕜 (E × F)) :
    ‖transpose (ContinuousLinearMap.inl 𝕜 E F) f‖ ≤ ‖f‖ := by
  apply (transpose (ContinuousLinearMap.inl 𝕜 E F) f).opNorm_le_bound (norm_nonneg f)
  intro x
  simpa using f.le_opNorm (x, (0 : F))

theorem norm_dual_product_right_le (f : StrongDual 𝕜 (E × F)) :
    ‖transpose (ContinuousLinearMap.inr 𝕜 E F) f‖ ≤ ‖f‖ := by
  apply (transpose (ContinuousLinearMap.inr 𝕜 E F) f).opNorm_le_bound (norm_nonneg f)
  intro y
  simpa using f.le_opNorm ((0 : E), y)

/-- The dual norm of a maximum-norm product is the sum of its coordinate
functional norms. -/
theorem norm_dual_product (f : StrongDual 𝕜 (E × F)) :
    ‖f‖ = ‖transpose (ContinuousLinearMap.inl 𝕜 E F) f‖ +
      ‖transpose (ContinuousLinearMap.inr 𝕜 E F) f‖ := by
  let f₁ := transpose (ContinuousLinearMap.inl 𝕜 E F) f
  let f₂ := transpose (ContinuousLinearMap.inr 𝕜 E F) f
  apply le_antisymm
  · apply f.opNorm_le_bound (add_nonneg (norm_nonneg f₁) (norm_nonneg f₂))
    rintro ⟨x, y⟩
    have hsplit : (x, y) = (x, (0 : F)) + ((0 : E), y) := by simp
    rw [show f (x, y) = f (x, 0) + f (0, y) by rw [hsplit, map_add]]
    calc
      ‖f (x, 0) + f (0, y)‖ ≤ ‖f (x, 0)‖ + ‖f (0, y)‖ := norm_add_le _ _
      _ ≤ ‖f₁‖ * ‖x‖ + ‖f₂‖ * ‖y‖ := add_le_add (f₁.le_opNorm x) (f₂.le_opNorm y)
      _ ≤ (‖f₁‖ + ‖f₂‖) * ‖(x, y)‖ := by
        have hx := norm_fst_le (x, y)
        have hy := norm_snd_le (x, y)
        nlinarith [norm_nonneg f₁, norm_nonneg f₂]
  · have hf₂ : ‖f₂‖ ≤ ‖f‖ := norm_dual_product_right_le f
    have hleft : ‖f₁‖ ≤ ‖f‖ - ‖f₂‖ := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (f := f₁) (sub_nonneg.mpr hf₂)
      intro x hx
      have hfx : ‖f₁ x‖ ≤ ‖f‖ := by
        simpa [f₁, hx] using f.le_opNorm (x, (0 : F))
      have hright : ‖f₂‖ ≤ ‖f‖ - ‖f₁ x‖ := by
        apply ContinuousLinearMap.opNorm_le_of_unit_norm (f := f₂) (sub_nonneg.mpr hfx)
        intro y hy
        have hxy := dual_product_evaluation_sum_le f x y hx.le hy.le
        change ‖f₁ x‖ + ‖f₂ y‖ ≤ ‖f‖ at hxy
        linarith
      linarith
    linarith

/-- Every functional on the product splits into its coordinate functionals. -/
theorem bidual_product_evaluation (z : Bidual 𝕜 (E × F)) (f : StrongDual 𝕜 (E × F)) :
    z f =
      bidualMap (ContinuousLinearMap.fst 𝕜 E F) z
        (transpose (ContinuousLinearMap.inl 𝕜 E F) f) +
      bidualMap (ContinuousLinearMap.snd 𝕜 E F) z
        (transpose (ContinuousLinearMap.inr 𝕜 E F) f) := by
  simp only [bidualMap_apply]
  rw [← map_add]
  apply congrArg z
  apply ContinuousLinearMap.ext
  rintro ⟨x, y⟩
  simpa only [ContinuousLinearMap.add_apply, transpose_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using f.map_add (x, 0) (0, y)

/-- The bidual of a maximum-norm product has the maximum of the two coordinate
bidual norms. -/
theorem norm_bidual_product (z : Bidual 𝕜 (E × F)) :
    ‖z‖ = max ‖bidualMap (ContinuousLinearMap.fst 𝕜 E F) z‖
      ‖bidualMap (ContinuousLinearMap.snd 𝕜 E F) z‖ := by
  let z₁ := bidualMap (ContinuousLinearMap.fst 𝕜 E F) z
  let z₂ := bidualMap (ContinuousLinearMap.snd 𝕜 E F) z
  apply le_antisymm
  · apply z.opNorm_le_bound (le_max_of_le_left (norm_nonneg z₁))
    intro f
    let f₁ := transpose (ContinuousLinearMap.inl 𝕜 E F) f
    let f₂ := transpose (ContinuousLinearMap.inr 𝕜 E F) f
    rw [bidual_product_evaluation]
    calc
      ‖z₁ f₁ + z₂ f₂‖ ≤ ‖z₁ f₁‖ + ‖z₂ f₂‖ := norm_add_le _ _
      _ ≤ ‖z₁‖ * ‖f₁‖ + ‖z₂‖ * ‖f₂‖ := add_le_add (z₁.le_opNorm f₁) (z₂.le_opNorm f₂)
      _ ≤ max ‖z₁‖ ‖z₂‖ * (‖f₁‖ + ‖f₂‖) := by
        nlinarith [le_max_left ‖z₁‖ ‖z₂‖, le_max_right ‖z₁‖ ‖z₂‖,
          norm_nonneg f₁, norm_nonneg f₂]
      _ = max ‖z₁‖ ‖z₂‖ * ‖f‖ := by rw [norm_dual_product f]
  · apply max_le
    · exact (norm_bidualMap_apply_le (ContinuousLinearMap.fst 𝕜 E F) z).trans
        ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_fst_le 𝕜 E F)
          (norm_nonneg z)).trans_eq (one_mul _))
    · exact (norm_bidualMap_apply_le (ContinuousLinearMap.snd 𝕜 E F) z).trans
        ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le 𝕜 E F)
          (norm_nonneg z)).trans_eq (one_mul _))

/-- Coordinate identification of the product bidual. -/
def bidualProductCoordinates : Bidual 𝕜 (E × F) →L[𝕜] (Bidual 𝕜 E × Bidual 𝕜 F) :=
  (bidualMap (ContinuousLinearMap.fst 𝕜 E F)).prod
    (bidualMap (ContinuousLinearMap.snd 𝕜 E F))

/-- The product-bidual coordinate map is isometric. -/
def bidualProductIsometry : Bidual 𝕜 (E × F) →ₗᵢ[𝕜] (Bidual 𝕜 E × Bidual 𝕜 F) :=
  { (bidualProductCoordinates (𝕜 := 𝕜) (E := E) (F := F)).toLinearMap with
    norm_map' := fun z => (norm_bidual_product z).symm }

/-- Reassemble two coordinate bidual vectors by their evaluation on product
functionals. -/
def bidualProductJoin (p : Bidual 𝕜 E × Bidual 𝕜 F) : Bidual 𝕜 (E × F) :=
  p.1.comp (transpose (ContinuousLinearMap.inl 𝕜 E F)) +
    p.2.comp (transpose (ContinuousLinearMap.inr 𝕜 E F))

theorem bidualProductJoin_coordinates (z : Bidual 𝕜 (E × F)) :
    bidualProductJoin (bidualProductCoordinates z) = z := by
  ext f
  change
    bidualMap (ContinuousLinearMap.fst 𝕜 E F) z
        (transpose (ContinuousLinearMap.inl 𝕜 E F) f) +
      bidualMap (ContinuousLinearMap.snd 𝕜 E F) z
        (transpose (ContinuousLinearMap.inr 𝕜 E F) f) = z f
  exact (bidual_product_evaluation z f).symm

theorem bidualProductCoordinates_join (p : Bidual 𝕜 E × Bidual 𝕜 F) :
    bidualProductCoordinates (bidualProductJoin p) = p := by
  apply Prod.ext
  · ext f
    change
      bidualMap (ContinuousLinearMap.fst 𝕜 E F)
        (bidualMap (ContinuousLinearMap.inl 𝕜 E F) p.1 +
          bidualMap (ContinuousLinearMap.inr 𝕜 E F) p.2) f = p.1 f
    simp only [map_add, ContinuousLinearMap.add_apply, bidualMap_apply]
    have hi : transpose (ContinuousLinearMap.inl 𝕜 E F)
        (transpose (ContinuousLinearMap.fst 𝕜 E F) f) = f := by ext x; rfl
    have hj : transpose (ContinuousLinearMap.inr 𝕜 E F)
        (transpose (ContinuousLinearMap.fst 𝕜 E F) f) = 0 := by
      ext y
      simp [transpose_apply]
    rw [hi, hj, map_zero, add_zero]
  · ext f
    change
      bidualMap (ContinuousLinearMap.snd 𝕜 E F)
        (bidualMap (ContinuousLinearMap.inl 𝕜 E F) p.1 +
          bidualMap (ContinuousLinearMap.inr 𝕜 E F) p.2) f = p.2 f
    simp only [map_add, ContinuousLinearMap.add_apply, bidualMap_apply]
    have hi : transpose (ContinuousLinearMap.inl 𝕜 E F)
        (transpose (ContinuousLinearMap.snd 𝕜 E F) f) = 0 := by
      ext x
      simp [transpose_apply]
    have hj : transpose (ContinuousLinearMap.inr 𝕜 E F)
        (transpose (ContinuousLinearMap.snd 𝕜 E F) f) = f := by ext y; rfl
    rw [hi, hj, map_zero, zero_add]

/-- The canonical isometric identification `(E × F)** ≃ E** × F**`, with
the maximum norm on both products. -/
def bidualProductEquiv : Bidual 𝕜 (E × F) ≃ₗᵢ[𝕜] (Bidual 𝕜 E × Bidual 𝕜 F) :=
  LinearIsometryEquiv.ofSurjective
    (R := 𝕜) (R₂ := 𝕜) (σ₁₂ := RingHom.id 𝕜) (σ₂₁ := RingHom.id 𝕜)
    (F := Bidual 𝕜 (E × F)) (E₂ := Bidual 𝕜 E × Bidual 𝕜 F)
    (bidualProductIsometry (𝕜 := 𝕜) (E := E) (F := F))
    (fun p => ⟨bidualProductJoin p, bidualProductCoordinates_join p⟩)

end LindenstraussRetraction
