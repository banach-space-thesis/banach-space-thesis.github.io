import NonCalkinAlgebra.TwistedFiniteSpan
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open BinaryPhase
universe u
variable {G : Type u} [AddCommGroup G]

def flip (c : Cocycle G) : Cocycle G where
  toFun g :=
    { toFun h := c h g
      map_zero' := by simp
      map_add' h k := by simp }
  map_zero' := by ext h; simp
  map_add' g k := by ext h; simp

@[simp] theorem flip_apply (c : Cocycle G) (g h : G) : flip c g h = c h g := rfl

/-- The canonical unit vector at a group element, with decidability kept
inside its noncomputable definition. -/
def delta (g : G) : SquareSummable G := by
  classical
  exact lp.single 2 g (1 : ℂ)

@[simp] theorem norm_delta (g : G) : ‖delta g‖ = 1 := by
  classical
  change ‖lp.single (E := fun _ : G => ℂ) 2 g (1 : ℂ)‖ = 1
  rw [lp.norm_single (by norm_num)]
  exact norm_one

theorem shift_delta_zero (c : Cocycle G) (g : G) : shift c g (delta 0) = delta g := by
  classical
  exact shift_single_zero c g

theorem cross_cocycle_step (c : Cocycle G) (g k z : G) :
    c g (z - g) + c (z - g - k) k = c (z - k) k + c g (z - k - g) := by
  have h1 : z - g = k + (z - g - k) := by abel
  have h2 : z - k = g + (z - g - k) := by abel
  have h3 : z - k - g = z - g - k := by abel
  have hleft : c g (z - g) = c g k + c g (z - g - k) := by
    conv_lhs => rw [h1, map_add]
  have hright : c (z - k) k = c g k + c (z - g - k) k := by
    conv_lhs => rw [h2, map_add, AddMonoidHom.add_apply]
  rw [hleft, hright, h3]
  abel

/-- Left and right twisted translations commute as actual bounded operators. -/
theorem shift_commutes_flip (c : Cocycle G) (g k : G) :
    shift c g * shift (flip c) k = shift (flip c) k * shift c g := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext z
  change phase (c g (z - g)) * (phase (c (z - g - k) k) * f (z - g - k)) =
    phase (c (z - k) k) * (phase (c g (z - k - g)) * f (z - k - g))
  have ht : z - k - g = z - g - k := by abel
  rw [ht]
  have hc := cross_cocycle_step c g k z
  rw [ht] at hc
  calc
    _ = phase (c g (z - g) + c (z - g - k) k) * f (z - g - k) := by
      rw [phase_add, mul_assoc]
    _ = phase (c (z - k) k + c g (z - g - k)) * f (z - g - k) := by rw [hc]
    _ = _ := by rw [phase_add, mul_assoc]

theorem closed_left_commutes_right (c : Cocycle G) (a : closedSubalgebra c) (k : G) :
    (a : SquareSummable G →L[ℂ] SquareSummable G) * shift (flip c) k =
      shift (flip c) k * (a : SquareSummable G →L[ℂ] SquareSummable G) := by
  let r := shift (flip c) k
  have hc : IsClosed {b : SquareSummable G →L[ℂ] SquareSummable G | b * r = r * b} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hs : (finiteSpan c : Set (SquareSummable G →L[ℂ] SquareSummable G)) ⊆
      {b | b * r = r * b} := by
    intro b hb
    change b ∈ Submodule.span ℂ _ at hb
    induction hb using Submodule.span_induction with
    | mem b hb => obtain ⟨g, rfl⟩ := hb; exact shift_commutes_flip c g k
    | zero => simp
    | add b d hb hd ihb ihd =>
      change (b + d) * r = r * (b + d)
      rw [add_mul, mul_add, ihb, ihd]
    | smul z b hb ih =>
      change (z • b) * r = r * (z • b)
      simpa only [smul_mul_assoc, mul_smul_comm] using congrArg (fun T => z • T) ih
  apply closure_minimal hs hc
  rw [← coe_closedSubalgebra_eq_closure]
  exact a.property

/-- The origin vector separates the closed left algebra. This uses the
commuting right translations and the full l2 sum, not only finite vectors. -/
theorem eq_zero_of_apply_delta_zero (c : Cocycle G) (a : closedSubalgebra c)
    (ha : (a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0) = 0) : a = 0 := by
  classical
  have hsingle : ∀ g : G, (a : SquareSummable G →L[ℂ] SquareSummable G) (delta g) = 0 := by
    intro g
    have h := congrArg (fun T : SquareSummable G →L[ℂ] SquareSummable G => T (delta 0))
      (closed_left_commutes_right c a g)
    change (a : SquareSummable G →L[ℂ] SquareSummable G) (shift (flip c) g (delta 0)) =
      shift (flip c) g ((a : SquareSummable G →L[ℂ] SquareSummable G) (delta 0)) at h
    rw [shift_delta_zero, ha, map_zero] at h
    exact h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  change (a : SquareSummable G →L[ℂ] SquareSummable G) f = 0
  have hsum := (lp.hasSum_single (by norm_num) f).mapL
    (a : SquareSummable G →L[ℂ] SquareSummable G)
  have hterms : (fun g : G => (a : SquareSummable G →L[ℂ] SquareSummable G)
      (lp.single 2 g (f g))) = fun _ : G => (0 : SquareSummable G) := by
    funext g
    have hrep : lp.single 2 g (f g) = (f g) • delta g := by
      simpa only [delta, smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : G => ℂ) 2 g (f g) (1 : ℂ))
    rw [hrep, map_smul, hsingle, smul_zero]
  rw [hterms] at hsum
  exact hsum.unique hasSum_zero

end NonCalkinAlgebra.TwistedRegular
