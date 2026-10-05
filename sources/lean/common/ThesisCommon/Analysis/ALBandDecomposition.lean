import ThesisCommon.Analysis.ALBandCoordinates

/-! A total disjoint family of principal bands gives an actual ordered ell-one
decomposition of the original complete real AL-lattice. -/
noncomputable section
open Set Filter Topology
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (a : I → E) (ha : ∀ i, 0 ≤ a i)
variable (hd : Pairwise (fun i j => |a i| ⊓ |a j| = 0))
variable (htotal : ∀ x : E, 0 ≤ x → (∀ i, x ⊓ a i = 0) → x = 0)

include ha htotal in
theorem alBandSynthesis_coordinates_of_nonneg (x : E) (hx : 0 ≤ x) :
    alBandSynthesis a (alBandCoordinates hAL a hd x) = x := by
  let v := alBandSynthesis a (alBandCoordinates hAL a hd x)
  have hvx : v ≤ x := by
    have hsum := (alBandSynthesis_summable a (alBandCoordinates hAL a hd x)).hasSum
    exact le_of_tendsto' hsum (fun s => alBandProjection_finite_sum_le a hd s x hx)
  have hz (i : I) : principalBandProjection (a i) (x-v) = 0 := by
    rw [map_sub]
    have h := principalBandProjection_alBandSynthesis a hd (alBandCoordinates hAL a hd x) i
    change principalBandProjection (a i) v = principalBandProjection (a i) x at h
    rw [h, sub_self]
  have hres : x-v = 0 := by
    apply htotal (x-v) (sub_nonneg.mpr hvx)
    intro i
    have h := (principalBandProjection_eq_zero_iff (a i) (x-v)).mp (hz i)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hvx), abs_of_nonneg (ha i)] using h
  exact (sub_eq_zero.mp hres).symm

include ha htotal in
theorem alBandSynthesis_coordinates (x : E) :
    alBandSynthesis a (alBandCoordinates hAL a hd x) = x := by
  calc
    alBandSynthesis a (alBandCoordinates hAL a hd x) =
        alBandSynthesis a (alBandCoordinates hAL a hd (x⁺-x⁻)) := by rw [posPart_sub_negPart]
    _ = alBandSynthesis a (alBandCoordinates hAL a hd x⁺) -
        alBandSynthesis a (alBandCoordinates hAL a hd x⁻) := by rw [map_sub, map_sub]
    _ = x⁺-x⁻ := by
      rw [alBandSynthesis_coordinates_of_nonneg hAL a ha hd htotal _ (posPart_nonneg x),
        alBandSynthesis_coordinates_of_nonneg hAL a ha hd htotal _ (negPart_nonneg x)]
    _ = x := posPart_sub_negPart x

def alBandLinearEquiv : E ≃ₗ[ℝ] lp (fun i => principalBand (a i)) 1 where
  toFun := alBandCoordinates hAL a hd
  invFun := alBandSynthesis a
  left_inv := alBandSynthesis_coordinates hAL a ha hd htotal
  right_inv := alBandCoordinates_alBandSynthesis hAL a hd
  map_add' := map_add (alBandCoordinates hAL a hd)
  map_smul' := map_smul (alBandCoordinates hAL a hd)

def alBandIsometryEquiv : E ≃ₗᵢ[ℝ] lp (fun i => principalBand (a i)) 1 :=
  { alBandLinearEquiv hAL a ha hd htotal with
    norm_map' := fun x => by
      apply le_antisymm (alBandCoefficients_norm_le hAL a hd x)
      have h := alBandSynthesis_norm_le a (alBandCoordinates hAL a hd x)
      rw [alBandSynthesis_coordinates hAL a ha hd htotal] at h
      exact h }

theorem alBandIsometryEquiv_nonneg_iff (x : E) :
    0 ≤ x ↔ ∀ i, 0 ≤ alBandIsometryEquiv hAL a ha hd htotal x i := by
  constructor
  · intro hx i
    exact principalBandProjection_nonneg (a i) x hx
  · intro hc
    rw [← alBandSynthesis_coordinates hAL a ha hd htotal x, alBandSynthesis_apply]
    exact tsum_nonneg (fun i => hc i)

end ThesisCommon
