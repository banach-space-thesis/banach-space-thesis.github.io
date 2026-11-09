import BanachIsometric.SignedSimplexStrictInterior

/-! Positive barycentric weights yield an interior point in the affine
coordinates used by the cone chart. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set

theorem signedSimplexDrop_mem_interior_of_positive (n : ℕ) (w : SignedCoordinateSimplex n)
    (hw : ∀ i, 0 < w i) : signedSimplexDrop n w ∈ interior (signedSimplexDomain n) := by
  apply mem_interior_signedSimplexDomain_of_pos n (fun j => hw j.succ)
  have hs := stdSimplex.sum_eq_one w
  rw [Fin.sum_univ_succ] at hs
  linarith [hw 0]

end BanachIsometric.SingularPrism
