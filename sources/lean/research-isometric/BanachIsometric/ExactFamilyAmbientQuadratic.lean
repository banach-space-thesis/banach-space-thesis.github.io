import BanachIsometric.ContinuousQuadratic
import BanachIsometric.ExactFamilyTopology

/-!
# Pair coverage transfers the reference quadratic form to the ambient gauge

The exact family supplies the same actual gauge on every range. If every
pair lies in one such range, its quadratic identity is the ambient
parallelogram identity. Continuity then reconstructs an actual quadratic form
on the original ambient real module. Its auxiliary norm is retained.
The pair-coverage input here is geometric; it is not a bundle-triviality or
degree theorem in disguise.
-/

namespace BanachIsometric

theorem quadraticForm_parallelogram {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Q : QuadraticForm ℝ E) (u v : E) :
    Q (u + v) + Q (u - v) = 2 * (Q u + Q v) := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hsub := hB u (-v)
  simp only [← sub_eq_add_neg, QuadraticMap.map_neg, map_neg] at hsub
  linarith [hB u v]

namespace ExactTangentialFamily

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {g : V → ℝ} {p : E → ℝ} (A : ExactTangentialFamily E V g p)

theorem exists_posDef_ambient_quadraticForm_of_pairwise_range
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    (Q : QuadraticForm ℝ E) (hQ : ∀ y, Q y = p y ^ 2)
    (hpair : ∀ x y : V, ∃ z, x ∈ Set.range (A.maps z) ∧ y ∈ Set.range (A.maps z)) :
    ∃ R : QuadraticForm ℝ V, R.PosDef ∧ ∀ x, R x = g x ^ 2 := by
  have hdiag (z) (u : E) : Q u = g (A.maps z u) ^ 2 := by rw [hQ, A.gauge_eq]
  have hsmul (a : ℝ) (x : V) : g (a • x) ^ 2 = a ^ 2 * g x ^ 2 := by
    obtain ⟨z, ⟨u, rfl⟩, _⟩ := hpair x 0
    rw [← map_smul, ← hdiag, ← hdiag, Q.map_smul]
    simp only [smul_eq_mul, pow_two]
  have hpara (x y : V) : g (x + y) ^ 2 + g (x - y) ^ 2 =
      2 * (g x ^ 2 + g y ^ 2) := by
    obtain ⟨z, ⟨u, rfl⟩, ⟨v, rfl⟩⟩ := hpair x y
    rw [← map_add, ← map_sub, ← hdiag, ← hdiag, ← hdiag, ← hdiag]
    exact quadraticForm_parallelogram Q u v
  obtain ⟨R, hR⟩ := exists_quadraticForm_of_continuous_parallelogram
    (fun x => g x ^ 2) (hcont.pow 2) (by
      change g 0 ^ 2 = 0
      rw [(hg.eq_zero_iff 0).mpr rfl]
      norm_num)
    hsmul hpara
  refine ⟨R, ?_, hR⟩
  intro x hx
  rw [hR]
  exact sq_pos_iff.mpr ((hg.eq_zero_iff x).not.mpr hx)

end ExactTangentialFamily
end BanachIsometric
