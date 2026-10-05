import ThesisCommon.Analysis.ALBandCoordinates
import ThesisCommon.Analysis.ALPrincipalFragmentDensity
import ThesisCommon.Analysis.ALRefinementPrincipalActions

/-! The principal band of a norm sum of disjoint generators is the actual
ell-one sum of their principal bands. Coordinates are the constructed band
projections; synthesis is the convergent sum of the ambient inclusions. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  (e : E) (a : I → E)
  (hband : ∀ i, principalBand (a i) ≤ principalBand e)
  (hd : Pairwise (fun i j => |a i| ⊓ |a j| = 0))
  (hsum : HasSum a e)

include hsum in
theorem principalBand_eq_zero_of_disjoint_generators {x : E}
    (hx : x ∈ principalBand e) (hdis : ∀ i, |x| ⊓ |a i| = 0) : x = 0 := by
  have hz (i : I) : principalBandProjection x (a i) = 0 :=
    (principalBandProjection_eq_zero_iff x (a i)).mpr (by rw [inf_comm]; exact hdis i)
  have ht : HasSum (fun _ : I => (0 : E)) (principalBandProjection x e) := by
    simpa only [hz] using (principalBandProjection x).hasSum hsum
  have he := (principalBandProjection_eq_zero_iff x e).mp (ht.unique hasSum_zero)
  have hpx := (principalBandProjection_eq_zero_iff e x).mpr (by rw [inf_comm]; exact he)
  change bandProjection (principalBand_orderClosed e) x = 0 at hpx
  rwa [(principalBand_orderClosed e).bandProjection_eq_self hx] at hpx

include hband in
theorem alBandSynthesis_mem_principalBand (x : lp (fun i => principalBand (a i)) 1) :
    alBandSynthesis a x ∈ principalBand e := by
  rw [alBandSynthesis_apply]
  apply (isClosed_principalBand e).mem_of_tendsto (alBandSynthesis_summable a x).hasSum
  apply Eventually.of_forall
  intro s
  exact (principalBand e).sum_mem (fun i _ => hband i (x i).property)

include hAL hband hd hsum in
theorem alBandSynthesis_coordinates_of_mem_principalBand {x : E} (hx : x ∈ principalBand e) :
    alBandSynthesis a (alBandCoordinates hAL a hd x) = x := by
  let v := alBandSynthesis a (alBandCoordinates hAL a hd x)
  have hv : v ∈ principalBand e := alBandSynthesis_mem_principalBand e a hband _
  have hz : x-v = 0 := by
    apply principalBand_eq_zero_of_disjoint_generators e a hsum ((principalBand e).sub_mem hx hv)
    intro i
    apply (principalBandProjection_eq_zero_iff (a i) (x-v)).mp
    rw [map_sub]
    have hi := principalBandProjection_alBandSynthesis a hd (alBandCoordinates hAL a hd x) i
    change principalBandProjection (a i) v = principalBandProjection (a i) x at hi
    rw [hi, sub_self]
  exact (sub_eq_zero.mp hz).symm

def alPrincipalBandCoordinates : principalBand e →L[ℝ] lp (fun i => principalBand (a i)) 1 :=
  (alBandCoordinates hAL a hd).comp (principalBand e).subtypeL

def alPrincipalBandSynthesis : lp (fun i => principalBand (a i)) 1 →L[ℝ] principalBand e :=
  (alBandSynthesis a).codRestrict (principalBand e) (alBandSynthesis_mem_principalBand e a hband)

theorem alPrincipalBandCoordinates_apply (x : principalBand e) (i : I) :
    (alPrincipalBandCoordinates hAL e a hd x i : E) = principalBandProjection (a i) x := rfl

theorem alPrincipalBandSynthesis_apply (x : lp (fun i => principalBand (a i)) 1) :
    (alPrincipalBandSynthesis e a hband x : E) = ∑' i, (x i : E) := rfl

include hsum in
theorem alPrincipalBandSynthesis_coordinates (x : principalBand e) :
    alPrincipalBandSynthesis e a hband (alPrincipalBandCoordinates hAL e a hd x) = x :=
  Subtype.ext (alBandSynthesis_coordinates_of_mem_principalBand hAL e a hband hd hsum x.property)

theorem alPrincipalBandCoordinates_synthesis (x : lp (fun i => principalBand (a i)) 1) :
    alPrincipalBandCoordinates hAL e a hd (alPrincipalBandSynthesis e a hband x) = x :=
  alBandCoordinates_alBandSynthesis hAL a hd x

def alPrincipalBandDecomposition : principalBand e ≃ₗᵢ[ℝ] lp (fun i => principalBand (a i)) 1 where
  toFun := alPrincipalBandCoordinates hAL e a hd
  invFun := alPrincipalBandSynthesis e a hband
  left_inv := alPrincipalBandSynthesis_coordinates hAL e a hband hd hsum
  right_inv := alPrincipalBandCoordinates_synthesis hAL e a hband hd
  map_add' := map_add (alPrincipalBandCoordinates hAL e a hd)
  map_smul' := map_smul (alPrincipalBandCoordinates hAL e a hd)
  norm_map' x := by
    apply le_antisymm (alBandCoefficients_norm_le hAL a hd x)
    have ht := alBandSynthesis_norm_le a (alBandCoordinates hAL a hd x)
    rw [alBandSynthesis_coordinates_of_mem_principalBand hAL e a hband hd hsum x.property] at ht
    exact ht

theorem alPrincipalBandDecomposition_apply (x : principalBand e) (i : I) :
    (alPrincipalBandDecomposition hAL e a hband hd hsum x i : E) =
      principalBandProjection (a i) x := rfl

theorem alPrincipalBandDecomposition_nonneg_iff (x : principalBand e) :
    (∀ i, 0 ≤ alPrincipalBandDecomposition hAL e a hband hd hsum x i) ↔ 0 ≤ x := by
  constructor
  · intro hx
    have heq := congrArg Subtype.val (alPrincipalBandSynthesis_coordinates hAL e a hband hd hsum x)
    change (∑' i, (alPrincipalBandCoordinates hAL e a hd x i : E)) = (x : E) at heq
    change 0 ≤ (x : E)
    rw [← heq]
    exact tsum_nonneg hx
  · intro hx i
    exact principalBandProjection_nonneg (a i) x hx

end ThesisCommon
