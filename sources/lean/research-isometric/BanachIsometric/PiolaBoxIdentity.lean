import BanachIsometric.PiolaWeightedFlux
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Smooth Piola flux across the two time faces of a box

A map with one constant output coordinate has zero Jacobian determinant. Its
weighted cofactor flux is therefore divergence free. The actual box divergence
theorem, with lateral flux removed by the target support condition, equates the
two remaining face integrals. This is the smooth homotopy integral step.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped BigOperators Topology Classical

theorem det_fderiv_eq_zero_of_constant_coordinate {n : ℕ}
    {F : PiolaSpace n → PiolaSpace n} {x : PiolaSpace n}
    (hF : DifferentiableAt ℝ F x) (j : Fin n) (c : ℝ)
    (hc : ∀ z, F z j = c) : (fderiv ℝ F x).det = 0 := by
  have hcoord := (ContinuousLinearMap.proj j : PiolaSpace n →L[ℝ] ℝ).hasFDerivAt.comp x
    hF.hasFDerivAt
  have hfun : (fun z => F z j) = (fun _ => c) := funext hc
  change HasFDerivAt (fun z => F z j)
    ((ContinuousLinearMap.proj j).comp (fderiv ℝ F x)) x at hcoord
  rw [hfun] at hcoord
  have hz := hcoord.unique (hasFDerivAt_const c x)
  rw [← det_piolaJacobian F x]
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro i
  have hi := congrArg (fun T : PiolaSpace n →L[ℝ] ℝ => T (piolaBasisVector i)) hz
  exact hi

def piolaBoxFace {n : ℕ} (a b : PiolaSpace (n + 1)) (i : Fin (n + 1)) :
    Set (PiolaSpace n) := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)

/-- The actual smooth cofactor-flux identity on a cylinder. The zero output
coordinate is the standard rank-deficient extension of a homotopy into one
extra ambient dimension; lateral vanishing is an ordinary support condition.
-/
theorem piola_box_time_faces_eq_of_constant_last {n : ℕ}
    {F : PiolaSpace (n + 1) → PiolaSpace (n + 1)} (hF : ContDiff ℝ 2 F)
    (hzero : ∀ x, F x (Fin.last n) = 0)
    {g : PiolaSpace (n + 1) → ℝ} (hg : ContDiff ℝ 1 g)
    (a b : PiolaSpace (n + 1)) (hab : a ≤ b)
    (hlat : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      ∀ z ∈ piolaBoxFace a b i,
        g (F (i.insertNth (b i) z)) = 0 ∧ g (F (i.insertNth (a i) z)) = 0) :
    (∫ z in piolaBoxFace a b (Fin.last n),
      (piolaJacobian F ((Fin.last n).insertNth (b (Fin.last n)) z)).adjugate
          (Fin.last n) (Fin.last n) *
        g (F ((Fin.last n).insertNth (b (Fin.last n)) z))) =
    ∫ z in piolaBoxFace a b (Fin.last n),
      (piolaJacobian F ((Fin.last n).insertNth (a (Fin.last n)) z)).adjugate
          (Fin.last n) (Fin.last n) *
        g (F ((Fin.last n).insertNth (a (Fin.last n)) z)) := by
  let V := weightedPiolaFlux F g (Fin.last n)
  let V' := fun x => weightedPiolaFluxDerivative F g x (Fin.last n)
  have hV (x : PiolaSpace (n + 1)) : HasFDerivAt V (V' x) x :=
    hasFDerivAt_weightedPiolaFlux hF x ((hg.differentiable le_rfl) (F x)) (Fin.last n)
  have htrace (x : PiolaSpace (n + 1)) :
      (∑ i : Fin (n + 1), V' x (Pi.single i 1) i) = 0 := by
    rw [← (hV x).fderiv]
    change coordinateDivergence V x = 0
    rw [weighted_piola_divergence hF x ((hg.differentiable le_rfl) (F x)) (Fin.last n)]
    rw [det_fderiv_eq_zero_of_constant_coordinate ((hF.differentiable (by norm_num)) x)
      (Fin.last n) 0 hzero, zero_mul]
  have htracefun : (fun x => ∑ i : Fin (n + 1), V' x (Pi.single i 1) i) =
      (fun _ => (0 : ℝ)) := funext htrace
  have hInt : IntegrableOn (fun x => ∑ i : Fin (n + 1), V' x (Pi.single i 1) i) (Icc a b) := by
    rw [htracefun]
    exact integrableOn_zero
  have hCont : ContinuousOn V (Icc a b) :=
    (show Differentiable ℝ V from fun x => (hV x).differentiableAt).continuous.continuousOn
  have hbox := integral_divergence_of_hasFDerivAt_off_countable a b hab V V'
    ∅ Set.countable_empty hCont (fun x _hx => hV x) hInt
  rw [htracefun, integral_zero] at hbox
  have hfaces (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
      ((∫ z in piolaBoxFace a b i, V (i.insertNth (b i) z) i) -
        ∫ z in piolaBoxFace a b i, V (i.insertNth (a i) z) i) = 0 := by
    have hf : (∫ z in piolaBoxFace a b i, V (i.insertNth (b i) z) i) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      change (piolaJacobian F (i.insertNth (b i) z)).adjugate i (Fin.last n) *
        g (F (i.insertNth (b i) z)) = 0
      rw [(hlat i hi z hz).1, mul_zero]
    have hb : (∫ z in piolaBoxFace a b i, V (i.insertNth (a i) z) i) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz
      change (piolaJacobian F (i.insertNth (a i) z)).adjugate i (Fin.last n) *
        g (F (i.insertNth (a i) z)) = 0
      rw [(hlat i hi z hz).2, mul_zero]
    rw [hf, hb, sub_self]
  have hsum : (∑ i : Fin (n + 1),
      ((∫ z in piolaBoxFace a b i, V (i.insertNth (b i) z) i) -
        ∫ z in piolaBoxFace a b i, V (i.insertNth (a i) z) i)) =
      ((∫ z in piolaBoxFace a b (Fin.last n), V ((Fin.last n).insertNth (b (Fin.last n)) z) (Fin.last n)) -
        ∫ z in piolaBoxFace a b (Fin.last n), V ((Fin.last n).insertNth (a (Fin.last n)) z) (Fin.last n)) := by
    apply Fintype.sum_eq_single (Fin.last n)
    intro i hi
    exact hfaces i hi
  change 0 = ∑ i : Fin (n + 1),
    ((∫ z in piolaBoxFace a b i, V (i.insertNth (b i) z) i) -
      ∫ z in piolaBoxFace a b i, V (i.insertNth (a i) z) i) at hbox
  rw [hsum] at hbox
  exact sub_eq_zero.mp hbox.symm

end BanachIsometric
