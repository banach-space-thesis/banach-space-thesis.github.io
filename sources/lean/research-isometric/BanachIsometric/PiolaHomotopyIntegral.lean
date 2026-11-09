import BanachIsometric.PiolaBoxIdentity
import BanachIsometric.PiolaTimeSlice
import BanachIsometric.PiolaTestLift

/-!
# Smooth signed-Jacobian homotopy identity

The box divergence identity is applied to the actual zero-coordinate extension
of a smooth homotopy. The actual last adjugate entry is the Jacobian of its
spatial slice, so the resulting face identity is an equality of the ordinary
signed-Jacobian integrals at the two endpoints.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped Classical

theorem integral_signedJacobian_piolaTimeSlice_eq {n : ℕ}
    {H : PiolaSpace (n + 1) → PiolaSpace n} (hH : ContDiff ℝ 2 H)
    {ψ : PiolaSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (a b : PiolaSpace (n + 1)) (hab : a ≤ b)
    (hlat : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      ∀ z ∈ piolaBoxFace a b i,
        ψ (H (i.insertNth (b i) z)) = 0 ∧ ψ (H (i.insertNth (a i) z)) = 0) :
    (∫ x in Icc (Fin.init a) (Fin.init b),
      (fderiv ℝ (piolaTimeSlice H (b (Fin.last n))) x).det *
        ψ (piolaTimeSlice H (b (Fin.last n)) x)) =
    ∫ x in Icc (Fin.init a) (Fin.init b),
      (fderiv ℝ (piolaTimeSlice H (a (Fin.last n))) x).det *
        ψ (piolaTimeSlice H (a (Fin.last n)) x) := by
  have hzero (z : PiolaSpace (n + 1)) :
      piolaHomotopyExtension H z (Fin.last n) = 0 := by
    simp [piolaHomotopyExtension]
  have hlat' : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      ∀ z ∈ piolaBoxFace a b i,
        piolaLiftTest ψ (piolaHomotopyExtension H (i.insertNth (b i) z)) = 0 ∧
          piolaLiftTest ψ (piolaHomotopyExtension H (i.insertNth (a i) z)) = 0 := by
    intro i hi z hz
    simpa only [piolaHomotopyExtension, piolaLiftTest_snoc] using hlat i hi z hz
  have hbox := piola_box_time_faces_eq_of_constant_last
    (contDiff_piolaHomotopyExtension hH) hzero (contDiff_piolaLiftTest hψ) a b hab hlat'
  have hface : piolaBoxFace a b (Fin.last n) = Icc (Fin.init a) (Fin.init b) := by
    simp only [piolaBoxFace, Fin.succAbove_last, Fin.init_def, Function.comp_def]
  have hcorner (x : PiolaSpace n) (t : ℝ) :
      (piolaJacobian (piolaHomotopyExtension H) (Fin.snoc x t)).adjugate
        (Fin.last n) (Fin.last n) = (fderiv ℝ (piolaTimeSlice H t) x).det :=
    adjugate_piolaHomotopyExtension_timeSlice H x t
      ((hH.differentiable (by norm_num)) (Fin.snoc x t))
  simpa only [hface, Fin.insertNth_last', hcorner, piolaHomotopyExtension,
    piolaLiftTest_snoc, piolaTimeSlice] using hbox

end BanachIsometric
