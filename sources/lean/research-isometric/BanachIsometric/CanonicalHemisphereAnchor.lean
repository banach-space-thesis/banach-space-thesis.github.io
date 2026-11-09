import BanachIsometric.CanonicalHemisphereFacetInteriors
import BanachIsometric.SuspensionBand
import BanachIsometric.AffineSubdivisionCarrier

/-! A concrete sphere direction hits exactly one north facet at positive
barycentric weights and hits none of the south facets. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_canonicalHemisphere_unique_north_anchor (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) :
    ∃ (x : sphere (0 : V) 1) (a : Fin (n + 3) × Simplex (n + 2)),
      (canonicalHemisphereFacet v v n hdim a.1 a.2).val = x ∧ (∀ j, 0 < a.2 j) ∧
      (∀ b : Fin (n + 3) × Simplex (n + 2),
        (canonicalHemisphereFacet v v n hdim b.1 b.2).val = x → b = a) ∧
      ∀ (i : Fin (n + 3)) (w : Simplex (n + 2)),
        (canonicalHemisphereFacet v (-v) n hdim i w).val ≠ x := by
  let u := simplexBarycenter (n + 1)
  have hu (j : Fin (n + 2)) : 0 < u j := by
    change 0 < 1 / ((n + 1 : ℕ) + 1 : ℝ)
    positivity
  let z := canonicalEquatorFace v n hdim 0 u
  have hz := canonicalEquatorOffSeam_of_positive_face v n hdim 0 u hu
  let t : Icc (-1 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  let x := equatorBand v (t, z)
  have hx : inner ℝ v.val x.val = t := equatorBand_inner v t z
  have ht : 0 < (t : ℝ) := by norm_num [t]
  let xN : closedHemisphere v := ⟨x, by
    change 0 ≤ inner ℝ v.val x.val
    rw [hx]
    exact ht.le⟩
  let r := Real.sqrt (1 - (t : ℝ) ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by norm_num [t])
  obtain ⟨a, ha, hpos, hunique⟩ := exists_canonicalHemisphereFacet_interior_and_unique v v (Or.inl rfl)
    n hdim xN t r ht hr z rfl hz
  refine ⟨x, a, congrArg Subtype.val ha, hpos, ?_, ?_⟩
  · intro b hb
    exact hunique b (Subtype.ext hb)
  · intro i w he
    have hn := (canonicalHemisphereFacet v (-v) n hdim i w).property
    change 0 ≤ inner ℝ (-v.val) (canonicalHemisphereFacet v (-v) n hdim i w).val.val at hn
    rw [he, inner_neg_left, hx] at hn
    linarith

end BanachIsometric.SingularPrism
