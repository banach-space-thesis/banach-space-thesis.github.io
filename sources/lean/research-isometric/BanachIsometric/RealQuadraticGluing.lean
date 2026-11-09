import BanachIsometric.GaugeNormModel
import BanachIsometric.FiniteConfigurations
import BanachIsometric.FunctionalStarBody
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! Norm-free real quadratic gluing through the actual diagonal. This uses
three-vector containment and bilinear polarization, without an ambient norm,
continuity premise or a global Jordan--von Neumann theorem. -/

namespace BanachIsometric

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

def realSquarePolar (p : X → ℝ) (x y : X) : ℝ :=
  (p (x + y) ^ 2 - p x ^ 2 - p y ^ 2) / 2

theorem associated_eq_realSquarePolar (Q : QuadraticForm ℝ X) {p : X → ℝ}
    (hQ : ∀ x, Q x = p x ^ 2) (x y : X) : Q.associated x y = realSquarePolar p x y := by
  let B := Q.associated
  have hdiag (z : X) : B z z = p z ^ 2 :=
    (QuadraticMap.associated_eq_self_apply ℝ Q z).trans (hQ z)
  have hsym : B x y = B y x := QuadraticMap.associated_isSymm ℝ Q x y
  have heq : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    rw [B.map_add, LinearMap.add_apply, (B x).map_add, (B y).map_add]
    ring
  change B x y = (p (x + y) ^ 2 - p x ^ 2 - p y ^ 2) / 2
  linarith [hdiag (x + y), hdiag x, hdiag y]

theorem positiveGaugeData_of_local_quadratic {p : X → ℝ} (hp : AlgebraicPositiveHomogeneous p)
    (m : ℕ) (hm3 : 3 ≤ m) (hm : (m : Cardinal) ≤ Module.rank ℝ X)
    (hlocal : ∀ Y : Submodule ℝ X, FiniteDimensional ℝ Y → Module.finrank ℝ Y = m →
      ∃ Q : QuadraticForm ℝ Y, ∀ y, Q y = p y.val ^ 2) :
    Nonempty (MetricGeometry.PositiveGaugeData p) := by
  have hsym (x y : X) : realSquarePolar p x y = realSquarePolar p y x := by
    unfold realSquarePolar
    rw [add_comm x y]
    ring
  have hdiag (x : X) : realSquarePolar p x x = p x ^ 2 := by
    obtain ⟨Y, hx, _, _, hfinite, hdim⟩ := exists_subspace_containing_triple (K := ℝ) m hm3 hm x 0 0
    obtain ⟨Q, hQ⟩ := hlocal Y hfinite hdim
    have hf := associated_eq_realSquarePolar Q hQ (⟨x, hx⟩ : Y) ⟨x, hx⟩
    have hd := (QuadraticMap.associated_eq_self_apply ℝ Q (⟨x, hx⟩ : Y)).trans (hQ ⟨x, hx⟩)
    exact hf.symm.trans hd
  have hadd (x y z : X) : realSquarePolar p x (y + z) = realSquarePolar p x y + realSquarePolar p x z := by
    obtain ⟨Y, hx, hy, hz, hfinite, hdim⟩ := exists_subspace_containing_triple (K := ℝ) m hm3 hm x y z
    obtain ⟨Q, hQ⟩ := hlocal Y hfinite hdim
    have hf (a b : Y) : Q.associated a b = realSquarePolar p a.val b.val := associated_eq_realSquarePolar Q hQ a b
    simpa only [hf] using (Q.associated (⟨x, hx⟩ : Y)).map_add (⟨y, hy⟩ : Y) ⟨z, hz⟩
  have hsmul (a : ℝ) (x y : X) : realSquarePolar p x (a • y) = a * realSquarePolar p x y := by
    obtain ⟨Y, hx, hy, _, hfinite, hdim⟩ := exists_subspace_containing_triple (K := ℝ) m hm3 hm x y 0
    obtain ⟨Q, hQ⟩ := hlocal Y hfinite hdim
    have hf (b c : Y) : Q.associated b c = realSquarePolar p b.val c.val := associated_eq_realSquarePolar Q hQ b c
    simpa only [hf, smul_eq_mul] using (Q.associated (⟨x, hx⟩ : Y)).map_smul a (⟨y, hy⟩ : Y)
  refine ⟨{
    bilinear := LinearMap.mk₂ ℝ (realSquarePolar p)
      (fun x y z => by rw [hsym, hadd, hsym z x, hsym z y])
      (fun a x y => by rw [hsym, hsmul, hsym y x]; rfl)
      hadd (fun a x y => by exact hsmul a x y)
    symmetric := hsym
    diagonal := hdiag
    nonneg := hp.nonneg
    eq_zero_iff := hp.eq_zero_iff
  }⟩

def MetricGeometry.PositiveGaugeData.quadraticForm {p : X → ℝ}
    (D : MetricGeometry.PositiveGaugeData p) : QuadraticForm ℝ X := LinearMap.BilinMap.toQuadraticMap D.bilinear

theorem MetricGeometry.PositiveGaugeData.quadraticForm_diagonal {p : X → ℝ}
    (D : MetricGeometry.PositiveGaugeData p) (x : X) : D.quadraticForm x = p x ^ 2 := D.diagonal x

theorem MetricGeometry.PositiveGaugeData.quadraticForm_posDef {p : X → ℝ}
    (D : MetricGeometry.PositiveGaugeData p) : D.quadraticForm.PosDef := by
  intro x hx
  rw [D.quadraticForm_diagonal]
  exact sq_pos_of_ne_zero ((D.eq_zero_iff x).not.mpr hx)

end
end BanachIsometric

