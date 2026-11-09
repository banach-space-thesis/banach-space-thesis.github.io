import BanachIsometric.AffineCarrierRealization
import Mathlib.Analysis.Normed.Module.Convex

/-! Actual support and diameter control for affine realization into a
convex subset with its inherited norm metric. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineCarrierRealization_supported {s : Set E} (hs : Convex ℝ s) (n : ℕ)
    (P : Set (Fin (n + 1) → E)) (Q : Set (RawSingularSimplex s n))
    (h : ∀ v (hv : ∀ i, v i ∈ s), v ∈ P → affineCarrierSimplex hs ⟨v, hv⟩ ∈ Q)
    (c : affineCarrier s n) (hc : c.val ∈ Finsupp.supported ℚ ℚ P) :
    affineCarrierRealization hs n c ∈ Finsupp.supported ℚ ℚ Q := by
  let e := Finsupp.supportedEquivFinsupp (M := ℚ) (R := ℚ)
    {v : Fin (n + 1) → E | ∀ i, v i ∈ s}
  have hc' : e c ∈ Finsupp.supported ℚ ℚ {v | v.val ∈ P} := by
    apply (Finsupp.mem_supported' ℚ _).mpr
    intro v hv
    change c.val v.val = 0
    exact (Finsupp.mem_supported' ℚ _).mp hc v.val hv
  have hmap : Finsupp.supported ℚ ℚ {v : {v : Fin (n + 1) → E // ∀ i, v i ∈ s} | v.val ∈ P} ≤
      (Finsupp.supported ℚ ℚ Q).comap (Finsupp.lmapDomain ℚ ℚ (affineCarrierSimplex hs)) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change Finsupp.lmapDomain ℚ ℚ (affineCarrierSimplex hs) (Finsupp.single v 1) ∈
      Finsupp.supported ℚ ℚ Q
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact Finsupp.single_mem_supported ℚ 1 (h v.val v.property hv)
  exact hmap hc'

theorem dist_affineCarrierSimplex_vertex_le {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : {v : Fin (n + 1) → E // ∀ i, v i ∈ s}) (D : ℝ)
    (hD : ∀ i j, dist (v.val i) (v.val j) ≤ D) (w : Simplex n) (i : Fin (n + 1)) :
    dist (affineCarrierSimplex hs v w) (⟨v.val i, v.property i⟩ : s) ≤ D := by
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge
    (affineSingularSimplex_mem_convexHull v.val w) (v.val i)
  exact hj.trans (hD j i)

theorem dist_affineCarrierSimplex_le {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : {v : Fin (n + 1) → E // ∀ i, v i ∈ s}) (D : ℝ)
    (hD : ∀ i j, dist (v.val i) (v.val j) ≤ D) (w z : Simplex n) :
    dist (affineCarrierSimplex hs v w) (affineCarrierSimplex hs v z) ≤ D := by
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hij⟩ := convexHull_exists_dist_ge2
    (affineSingularSimplex_mem_convexHull v.val w) (affineSingularSimplex_mem_convexHull v.val z)
  exact hij.trans (hD i j)

end BanachIsometric.SingularPrism
