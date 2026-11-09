import BanachIsometric.SignedIndexNormalization
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Actual affine equivalences have their derivative's signed index at the
image of every interior source point. This follows from their actual unique
fibers, with no degree normalization postulate. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology NNReal

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem signedFiberCount_of_injective_mem
    (f : E → E) (D : E → E →L[ℝ] E) (s : Set E) (hf : Function.Injective f)
    {x : E} (hx : x ∈ s) :
    signedFiberCount f D s (f x) = (SignType.sign (D x).det : ℤ) := by
  classical
  have hset : {z : E | z ∈ s ∧ f z = f x} = {x} := by
    ext z
    constructor
    · intro hz
      exact hf hz.2
    · intro hz
      subst z
      exact ⟨hx, rfl⟩
  have hfin : {z : E | z ∈ s ∧ f z = f x}.Finite := hset.symm ▸ finite_singleton x
  have hsum : signedFiberSum f D s (f x) = (SignType.sign (D x).det : ℝ) := by
    unfold signedFiberSum
    change (∑' z : {z : E | z ∈ s ∧ f z = f x}, jacobianOrientation D z.val) = _
    rw [hset]
    rw [tsum_singleton]
    rfl
  have hc := signedFiberSum_eq_coe_signedFiberCount f D s (f x) hfin
  rw [hsum] at hc
  have hh : ((signedFiberCount f D s (f x) : ℤ) : ℝ) =
      ((SignType.sign (D x).det : ℤ) : ℝ) := by
    simpa only [SignType.intCast_cast] using hc.symm
  exact_mod_cast hh

def affineLinearization (L : E ≃L[ℝ] E) (x c z : E) : E := c + L (z - x)

theorem hasFDerivAt_affineLinearization (L : E ≃L[ℝ] E) (x c z : E) :
    HasFDerivAt (affineLinearization L x c) (L : E →L[ℝ] E) z := by
  have hfun : affineLinearization L x c = fun v => (c - L x) + L v := by
    funext v
    rw [affineLinearization, map_sub]
    abel
  rw [hfun]
  exact L.hasFDerivAt.const_add (c - L x)

theorem affineLinearization_injective (L : E ≃L[ℝ] E) (x c : E) :
    Function.Injective (affineLinearization L x c) := by
  intro z w h
  have hh : z - x = w - x := L.injective (add_left_cancel h)
  simpa only [sub_add_cancel] using congrArg (fun v => v + x) hh

end General

theorem localSignedIndex_affineLinearization
    {n : ℕ} [NeZero n] (L : PiolaSpace n ≃L[ℝ] PiolaSpace n)
    (x c a b : PiolaSpace n) (hab : a ≤ b) (hx : x ∈ interior (Icc a b)) :
    localSignedIndex (affineLinearization L x c) a b c =
      (SignType.sign (L : PiolaSpace n →L[ℝ] PiolaSpace n).det : ℤ) := by
  let F := affineLinearization L x c
  have hF : LipschitzWith _ F := (LipschitzWith.const c).add
    (L.lipschitz.comp ((LipschitzWith.id).sub (LipschitzWith.const x)))
  have hcenter : F x = c := by simp only [F, affineLinearization, sub_self, map_zero, add_zero]
  have hc : c ∉ F '' piolaBoxBoundary a b := by
    rintro ⟨z, hz, hzc⟩
    have hzx := affineLinearization_injective L x c (hzc.trans hcenter.symm)
    subst z
    rw [piolaBoxBoundary_eq_frontier] at hz
    exact hz.2 hx
  let pre : PiolaSpace n → PiolaSpace n := fun y => x + L.symm (y - c)
  have hpre (y : PiolaSpace n) : F (pre y) = y := by
    dsimp [F, pre, affineLinearization]
    rw [add_sub_cancel_left, L.apply_symm_apply, add_sub_cancel]
  have hprecont : Continuous pre := continuous_const.add
    (L.symm.continuous.comp (continuous_id.sub continuous_const))
  have hopen : IsOpen {y | pre y ∈ interior (Icc a b)} := isOpen_interior.preimage hprecont
  have hcpre : c ∈ {y | pre y ∈ interior (Icc a b)} := by
    simpa only [pre, mem_setOf_eq, sub_self, map_zero, add_zero] using hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen c hcpre
  have hder : fderiv ℝ F = fun _ => (L : PiolaSpace n →L[ℝ] PiolaSpace n) := by
    funext z
    exact (hasFDerivAt_affineLinearization L x c z).fderiv
  apply localSignedIndex_eq_of_ae_eq_on_ball hF a b hab c hc hr
  apply ae_of_all
  intro y hy
  have hmem : pre y ∈ Icc a b := interior_subset (hball hy)
  rw [hder]
  have hcount := signedFiberCount_of_injective_mem F
    (fun _ => (L : PiolaSpace n →L[ℝ] PiolaSpace n)) (Icc a b)
    (affineLinearization_injective L x c) hmem
  rwa [hpre y] at hcount

end BanachIsometric
