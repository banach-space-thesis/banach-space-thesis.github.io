import BanachIsometric.RawSingularChains
import Mathlib.Analysis.Convex.Combination

/-! Literal affine singular simplices. These will be used to construct
barycentric subdivision before pushing it forward along arbitrary continuous
singular simplices. The coordinate formula is natural for every vertex map. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) : RawSingularSimplex E n where
  toFun w := ∑ i, w i • v i
  continuous_toFun := continuous_finset_sum _ (fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)

theorem affineSingularSimplex_precomp {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (v : Fin (b + 1) → E) :
    (affineSingularSimplex v).comp (simplexMap f) = affineSingularSimplex (v ∘ f) := by
  classical
  apply ContinuousMap.ext
  intro w
  change (∑ j, FunOnFinite.linearMap ℝ ℝ f w.val j • v j) = ∑ i, w i • v (f i)
  simp_rw [FunOnFinite.linearMap_apply_apply, Finset.sum_smul, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp
  rfl

theorem affineSingularSimplex_mem_convexHull {n : ℕ} (v : Fin (n + 1) → E) (w : Simplex n) :
    affineSingularSimplex v w ∈ convexHull ℝ (Set.range v) := by
  change (∑ i, w.val i • v i) ∈ _
  rw [← Finset.univ.centerMass_eq_of_sum_1 v w.property.2]
  exact Finset.univ.centerMass_mem_convexHull (fun i _ => w.property.1 i)
    (w.property.2.symm ▸ zero_lt_one) (fun i _ => Set.mem_range_self i)

theorem affineSingularSimplex_mem_convex {n : ℕ} {s : Set E} (hs : Convex ℝ s)
    (v : Fin (n + 1) → E) (hv : ∀ i, v i ∈ s) (w : Simplex n) :
    affineSingularSimplex v w ∈ s :=
  (convexHull_min (Set.range_subset_iff.mpr hv) hs) (affineSingularSimplex_mem_convexHull v w)

def affineSimplexMap {a b : ℕ} (v : Fin (a + 1) → Simplex b) : C(Simplex a, Simplex b) where
  toFun w := ⟨affineSingularSimplex (fun i => (v i).val) w,
    affineSingularSimplex_mem_convex (convex_stdSimplex ℝ (Fin (b + 1)))
      (fun i => (v i).val) (fun i => (v i).property) w⟩
  continuous_toFun := (affineSingularSimplex _).continuous.subtype_mk _

end BanachIsometric.SingularPrism
