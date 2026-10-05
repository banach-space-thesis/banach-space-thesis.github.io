import Posets.FiniteIncidenceRepresentation
import Posets.IncidenceDiagonal

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P] [LocallyFiniteOrder P]

/-- The paper's unbounded diagonal and point idempotents exclude every
submultiplicative algebra norm, without imposing an ambient topology. -/
theorem infinite_incidence_not_normable [Infinite P] :
    ¬ AlgebraNormExists 𝕜 (IncidenceAlgebra 𝕜 P) := by
  rintro ⟨N, hnonneg, hzero, _, hsmul, hmul⟩
  let e := Infinite.natEmbedding P
  let a : P → 𝕜 := Function.extend e (fun n : ℕ => (n : 𝕜)) (fun _ => 0)
  have ha (n : ℕ) : a (e n) = (n : 𝕜) := e.injective.extend_apply _ _ n
  let f := incidenceDiagonal a
  have hbound (n : ℕ) : (n : ℝ) ≤ N f := by
    let g : IncidenceAlgebra 𝕜 P := incidenceDiagonal (Pi.single (e n) 1)
    have hg : g ≠ 0 := incidenceDiagonal_point_ne_zero (e n)
    have hpos : 0 < N g := lt_of_le_of_ne (hnonneg g) (Ne.symm ((hzero g).not.mpr hg))
    have hfg : f * g = (n : 𝕜) • g := by
      simpa only [f, g, ha] using incidenceDiagonal_mul_point a (e n)
    have hb := hmul f g
    rw [hfg, hsmul, RCLike.norm_natCast] at hb
    exact (mul_le_mul_iff_left₀ hpos).mp hb
  obtain ⟨n, hn⟩ := exists_nat_gt (N f)
  exact (not_lt_of_ge (hbound n)) hn

/-- Proposition 6.8 in both directions, including the empty finite poset. -/
theorem proposition_6_8_proof (𝕜 : Type) [RCLike 𝕜] (P : Type)
    [PartialOrder P] [LocallyFiniteOrder P] : Proposition_6_8 𝕜 P := by
  constructor
  · intro hnorm
    by_contra hfinite
    haveI : Infinite P := not_finite_iff_infinite.mp hfinite
    exact infinite_incidence_not_normable hnorm
  · intro hfinite
    letI := hfinite
    letI := Fintype.ofFinite P
    exact finite_incidence_normable

end Posets
