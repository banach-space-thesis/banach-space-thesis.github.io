import PL1.IntrinsicGraph
import PL1.L1Sum
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Commuting finite-dimensional approximations of the actual intrinsic graph -/

noncomputable section
open Filter
open scoped Topology

namespace PL1.IntrinsicGraph

variable {𝕜 Y : Type*} [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (D : ℕ → Y →L[𝕜] Y) (h0 : D 0 = ContinuousLinearMap.id 𝕜 Y)
variable (T : Y →L[𝕜] Y) (hc : ∀ n y, T (D n y) = D n (T y))

include hc in
theorem summable_commuting_image (x : Space D) :
    Summable (fun n => ‖D n (T (evalZero D x))‖) := by
  apply ((L1Sum.summable_norm (x : Ambient (Y := Y))).mul_left ‖T‖).of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    rw [← hc, ← coord_eq]
    exact T.le_opNorm _

def commutingLiftLinear : Space D →ₗ[𝕜] Space D where
  toFun x := ofSummable D h0 (T (evalZero D x)) (summable_commuting_image D T hc x)
  map_add' x y := by
    apply evalZero_injective D
    simp only [evalZero_ofSummable, map_add]
  map_smul' c x := by
    apply evalZero_injective D
    simp only [evalZero_ofSummable, map_smul, RingHom.id_apply]

theorem norm_commutingLiftLinear_le (x : Space D) :
    ‖commutingLiftLinear D h0 T hc x‖ ≤ ‖T‖ * ‖x‖ := by
  change ‖ofSummable D h0 (T (evalZero D x)) (summable_commuting_image D T hc x)‖ ≤ _
  rw [norm_ofSummable, norm_eq_tsum, ← tsum_mul_left]
  apply (summable_commuting_image D T hc x).tsum_le_tsum _
    ((L1Sum.summable_norm (x : Ambient (Y := Y))).mul_left ‖T‖)
  intro n
  rw [← hc, ← coord_eq]
  exact T.le_opNorm _

def commutingLift : Space D →L[𝕜] Space D :=
  (commutingLiftLinear D h0 T hc).mkContinuous ‖T‖ (norm_commutingLiftLinear_le D h0 T hc)

@[simp] theorem evalZero_commutingLift (x : Space D) :
    evalZero D (commutingLift D h0 T hc x) = T (evalZero D x) :=
  evalZero_ofSummable D h0 _ (summable_commuting_image D T hc x)

@[simp] theorem coord_commutingLift (n : ℕ) (x : Space D) :
    coord D n (commutingLift D h0 T hc x) = T (coord D n x) := by
  change D n (T (evalZero D x)) = T (coord D n x)
  rw [← hc, coord_eq]

theorem norm_commutingLift_le : ‖commutingLift D h0 T hc‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    (norm_commutingLiftLinear_le D h0 T hc)

theorem commutingLift_isProjection (hT : IsProjection T) :
    IsProjection (commutingLift D h0 T hc) := by
  apply ContinuousLinearMap.ext
  intro x
  apply evalZero_injective D
  simp only [ContinuousLinearMap.comp_apply, evalZero_commutingLift]
  exact DFunLike.congr_fun hT (evalZero D x)

theorem commutingLift_comp_eq_left (U : Y →L[𝕜] Y)
    (hu : ∀ n y, U (D n y) = D n (U y)) (hTU : T.comp U = T) :
    (commutingLift D h0 T hc).comp (commutingLift D h0 U hu) =
      commutingLift D h0 T hc := by
  apply ContinuousLinearMap.ext
  intro x
  apply evalZero_injective D
  simp only [ContinuousLinearMap.comp_apply, evalZero_commutingLift]
  exact DFunLike.congr_fun hTU (evalZero D x)

def commutingLiftRangeMap : (commutingLift D h0 T hc).range →ₗ[𝕜] T.range :=
    ((evalZero D).toLinearMap.comp (commutingLift D h0 T hc).range.subtype).codRestrict _ (by
      rintro ⟨x, y, hy⟩
      refine ⟨evalZero D y, ?_⟩
      change T (evalZero D y) = evalZero D x
      rw [← hy]
      exact (evalZero_commutingLift D h0 T hc y).symm)

theorem commutingLiftRangeMap_injective :
    Function.Injective (commutingLiftRangeMap D h0 T hc) := by
  intro x y h
  apply Subtype.ext
  apply evalZero_injective D
  exact congrArg Subtype.val h

theorem commutingLift_range_finiteDimensional [FiniteDimensional 𝕜 T.range] :
    FiniteDimensional 𝕜 (commutingLift D h0 T hc).range :=
  FiniteDimensional.of_injective (commutingLiftRangeMap D h0 T hc)
    (commutingLiftRangeMap_injective D h0 T hc)

theorem finrank_commutingLift_range_le [FiniteDimensional 𝕜 T.range] :
    Module.finrank 𝕜 (commutingLift D h0 T hc).range ≤ Module.finrank 𝕜 T.range :=
  LinearMap.finrank_le_finrank_of_injective (commutingLiftRangeMap_injective D h0 T hc)

theorem commutingLift_tendsto
    (S : ℕ → Y →L[𝕜] Y) (hS : ∀ m, ‖S m‖ ≤ 1)
    (hcomm : ∀ m n y, S m (D n y) = D n (S m y))
    (hstrong : ∀ y, Tendsto (fun m => S m y) atTop (𝓝 y)) (x : Space D) :
    Tendsto (fun m => commutingLift D h0 (S m) (hcomm m) x) atTop (𝓝 x) := by
  have hsum : Summable (fun n => 2 * ‖coord D n x‖) :=
    (L1Sum.summable_norm (x : Ambient (Y := Y))).mul_left 2
  have ht : Tendsto (fun m => ∑' n, ‖S m (coord D n x) - coord D n x‖) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun m n => ‖S m (coord D n x) - coord D n x‖)
      (g := fun _ : ℕ => (0 : ℝ)) (𝓕 := atTop) hsum
      (fun n => by simpa only [sub_self, norm_zero] using
        ((hstrong (coord D n x)).sub (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => coord D n x) atTop (𝓝 (coord D n x)))).norm)
      (Eventually.of_forall (fun m n => by
        rw [norm_norm]
        have hbound : ‖S m (coord D n x)‖ ≤ ‖coord D n x‖ :=
          ((S m).le_opNorm _).trans (by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hS m) (norm_nonneg _))
        exact (norm_sub_le _ _).trans (by linarith)))
    simpa only [tsum_zero] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_eq_tsum, map_sub, coord_commutingLift] using ht

end PL1.IntrinsicGraph
