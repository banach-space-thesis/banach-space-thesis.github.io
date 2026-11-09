import BanachIsometric.QuaternionicHyperplaneField

/-! Quaternionic Riesz representation is proved from actual finite right
coordinates. It turns an annihilating right-linear functional into an actual
unit normal, supplying pair coverage without a quaternionic Hilbert typeclass. -/

namespace BanachIsometric.Quaternionic

open Module
open scoped Quaternion

noncomputable section

def standardBasis (m : ℕ) : Basis (Fin m) Hᵐᵒᵖ (Euclidean m) :=
  Basis.ofEquivFun (scalarCoordinates m)

@[simp] theorem standardBasis_repr (m : ℕ) (v : Euclidean m) (r : Fin m) :
    (standardBasis m).repr v r = MulOpposite.op (v r) := rfl

theorem exists_standardHermitian_representative (m : ℕ)
    (f : Euclidean m →ₗ[Hᵐᵒᵖ] Hᵐᵒᵖ) :
    ∃ u : Euclidean m, ∀ v, (standardHermitian m).form u v = MulOpposite.unop (f v) := by
  let u : Euclidean m := WithLp.toLp 2 fun r => star (MulOpposite.unop (f (standardBasis m r)))
  have hf (v : Euclidean m) : f v = ∑ r, MulOpposite.op (v r) * f (standardBasis m r) := by
    conv_lhs => rw [← (standardBasis m).sum_repr v]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, standardBasis_repr]
  refine ⟨u, ?_⟩
  intro v
  change (∑ r, star (star (MulOpposite.unop (f (standardBasis m r)))) * v r) = MulOpposite.unop (f v)
  simp only [star_star]
  rw [hf v, Finset.unop_sum]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

theorem exists_unit_standardHermitian_annihilating_pair (m : ℕ) (hm : 3 ≤ m)
    (x y : Euclidean m) :
    ∃ u : Euclidean m, ‖u‖ = 1 ∧ (standardHermitian m).form u x = 0 ∧
      (standardHermitian m).form u y = 0 := by
  obtain ⟨f, hf, hfx, hfy⟩ := exists_nonzero_functional_annihilating_pair
    (K := Hᵐᵒᵖ) (V := Euclidean m) (by rwa [finrank_right_euclidean]) x y
  obtain ⟨u, hu⟩ := exists_standardHermitian_representative m f
  have hune : u ≠ 0 := by
    intro hz
    apply hf
    apply LinearMap.ext
    intro v
    apply MulOpposite.unop_injective
    change MulOpposite.unop (f v) = 0
    have h := hu v
    rw [hz] at h
    simpa only [standardHermitian, PiLp.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] using h.symm
  have hzero (v : Euclidean m) (hv : f v = 0) :
      (standardHermitian m).form (NormedSpace.normalize u) v = 0 := by
    change (standardHermitian m).form (‖u‖⁻¹ • u) v = 0
    rw [← rightMul_real u (‖u‖⁻¹), (standardHermitian m).mul_left, hu, hv]
    exact mul_zero _
  exact ⟨NormedSpace.normalize u, NormedSpace.norm_normalize hune, hzero x hfx, hzero y hfy⟩

end
end BanachIsometric.Quaternionic
