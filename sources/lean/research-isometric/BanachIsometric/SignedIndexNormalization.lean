import BanachIsometric.LocalSignedIndex
import BanachIsometric.SignedCountExcision
import BanachIsometric.SignedFiberNormalization
import BanachIsometric.PiolaBoxFrontier

/-!
# Normalisation of the canonical actual signed index

Outside the actual source image the index is zero. For a genuine real linear
equivalence it is the actual determinant sign at interior image points. The
identity consequently has index one, proved from its fibers.
-/

namespace BanachIsometric

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

variable {n : ℕ} [NeZero n]

theorem localSignedIndex_eq_zero_of_not_mem_image
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n) (hc : c ∉ f '' Icc a b) :
    localSignedIndex f a b c = 0 := by
  have hcb : c ∉ f '' piolaBoxBoundary a b := by
    intro h
    obtain ⟨x, hx, hxc⟩ := h
    exact hc ⟨x, hx.1, hxc⟩
  have hopen : IsOpen (f '' Icc a b)ᶜ :=
    (isCompact_Icc.image hf.continuous).isClosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen c hc
  apply localSignedIndex_eq_of_ae_eq_on_ball hf a b hab c hcb hr
  apply ae_of_all
  intro y hy
  exact signedFiberCount_eq_zero_of_not_mem_image f (fderiv ℝ f) (Icc a b) y (hball hy)

theorem localSignedIndex_linearEquiv
    (A : PiolaSpace n ≃L[ℝ] PiolaSpace n) (a b : PiolaSpace n) (hab : a ≤ b)
    (c : PiolaSpace n) (hc : c ∉ A '' piolaBoxBoundary a b)
    (hint : c ∈ interior (A '' Icc a b)) :
    localSignedIndex A a b c = (SignType.sign (A : PiolaSpace n →L[ℝ] PiolaSpace n).det : ℤ) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hint
  apply localSignedIndex_eq_of_ae_eq_on_ball A.lipschitz a b hab c hc hr
  apply ae_of_all
  intro y hy
  have hmem : A.symm y ∈ Icc a b := by
    obtain ⟨x, hx, hxy⟩ := interior_subset (hball hy)
    simpa only [← hxy, A.symm_apply_apply] using hx
  have hder : fderiv ℝ (A : PiolaSpace n → PiolaSpace n) =
      fun _ => (A : PiolaSpace n →L[ℝ] PiolaSpace n) := by
    funext x
    exact A.fderiv
  rw [hder, signedFiberCount_linearEquiv, if_pos hmem]

theorem localSignedIndex_id (a b : PiolaSpace n) (hab : a ≤ b)
    (c : PiolaSpace n) (hc : c ∈ interior (Icc a b)) :
    localSignedIndex (id : PiolaSpace n → PiolaSpace n) a b c = 1 := by
  have hcb : c ∉ (ContinuousLinearEquiv.refl ℝ (PiolaSpace n)) '' piolaBoxBoundary a b := by
    simpa only [ContinuousLinearEquiv.refl_apply, image_id', piolaBoxBoundary_eq_frontier] using
      (show c ∉ frontier (Icc a b) from fun h => h.2 hc)
  have hd : (ContinuousLinearMap.id ℝ (PiolaSpace n)).det = 1 := by
    change LinearMap.det (1 : Module.End ℝ (PiolaSpace n)) = 1
    exact map_one (LinearMap.det : Module.End ℝ (PiolaSpace n) →* ℝ)
  simpa [hd] using localSignedIndex_linearEquiv (ContinuousLinearEquiv.refl ℝ (PiolaSpace n))
    a b hab c hcb (by simpa using hc)

end BanachIsometric
