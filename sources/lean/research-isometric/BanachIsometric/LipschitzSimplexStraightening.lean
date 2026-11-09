import BanachIsometric.LipschitzIntervalInterpolation
import BanachIsometric.LipschitzNeighborhoodRetraction
import BanachIsometric.LipschitzAffineSimplex

/-! A simplex inside a convex part of an ambient retraction domain can be
straightened to the retracted affine combination of its vertices. Both
the straightening and its interpolation respect every vertex map. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set
open scoped Topology unitInterval NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def simplexVertexAffine {s : Set E} {n : ℕ} (simplex : RawSingularSimplex s n) :
    RawSingularSimplex E n :=
  affineSingularSimplex (fun i => (simplex (stdSimplex.vertex i)).val)

theorem simplexVertexAffine_precomp {s : Set E} {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (simplex : RawSingularSimplex s b) :
    (simplexVertexAffine simplex).comp (simplexMap f) =
      simplexVertexAffine (simplex.comp (simplexMap f)) := by
  unfold simplexVertexAffine
  rw [affineSingularSimplex_precomp]
  congr 1
  funext i
  change (simplex (stdSimplex.vertex (f i))).val =
    (simplex (stdSimplex.map f (stdSimplex.vertex i))).val
  rw [stdSimplex.map_vertex]

def SimplexFitsConvexDomain {s : Set E} (U : Set E) {n : ℕ} (simplex : RawSingularSimplex s n) : Prop :=
  ∃ V : Set E, Convex ℝ V ∧ V ⊆ U ∧ ∀ w, (simplex w).val ∈ V

theorem simplexFitsConvexDomain_precomp {s U : Set E} {a b : ℕ}
    (f : Fin (a + 1) → Fin (b + 1)) {simplex : RawSingularSimplex s b}
    (h : SimplexFitsConvexDomain U simplex) : SimplexFitsConvexDomain U (simplex.comp (simplexMap f)) := by
  obtain ⟨V, hV, hVU, hσ⟩ := h
  exact ⟨V, hV, hVU, fun w => hσ (simplexMap f w)⟩

theorem simplexVertexAffine_mem_convex {s V : Set E} {n : ℕ}
    (simplex : RawSingularSimplex s n) (hV : Convex ℝ V)
    (hσ : ∀ w, (simplex w).val ∈ V) (w : Simplex n) : simplexVertexAffine simplex w ∈ V :=
  affineSingularSimplex_mem_convex hV _ (fun i => hσ (stdSimplex.vertex i)) w

theorem simplexVertexAffine_mem_domain {s U : Set E} {n : ℕ}
    {simplex : RawSingularSimplex s n} (h : SimplexFitsConvexDomain U simplex)
    (w : Simplex n) : simplexVertexAffine simplex w ∈ U := by
  obtain ⟨V, hV, hVU, hσ⟩ := h
  exact hVU (simplexVertexAffine_mem_convex simplex hV hσ w)

def simplexVertexInterpolation {s : Set E} {n : ℕ} (simplex : RawSingularSimplex s n) :
    C(unitInterval × Simplex n, E) where
  toFun z := (1 - (z.1 : ℝ)) • (simplex z.2).val + (z.1 : ℝ) • simplexVertexAffine simplex z.2
  continuous_toFun :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      ((continuous_subtype_val.comp simplex.continuous).comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((simplexVertexAffine simplex).continuous.comp continuous_snd))

theorem simplexVertexInterpolation_mem_domain {s U : Set E} {n : ℕ}
    {simplex : RawSingularSimplex s n} (h : SimplexFitsConvexDomain U simplex)
    (z : unitInterval × Simplex n) : simplexVertexInterpolation simplex z ∈ U := by
  obtain ⟨V, hV, hVU, hσ⟩ := h
  apply hVU
  exact hV (hσ z.2) (simplexVertexAffine_mem_convex simplex hV hσ z.2)
    (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel _ _)

namespace LipschitzNeighborhoodRetraction

variable {s : Set E} (D : LipschitzNeighborhoodRetraction s)

def straighten {n : ℕ} (simplex : RawSingularSimplex s n)
    (h : SimplexFitsConvexDomain D.domain simplex) : RawSingularSimplex s n := by
  let lift : C(Simplex n, D.domain) :=
    ⟨fun w => ⟨simplexVertexAffine simplex w, simplexVertexAffine_mem_domain h w⟩,
      (simplexVertexAffine simplex).continuous.subtype_mk (simplexVertexAffine_mem_domain h)⟩
  exact D.retract.comp lift

def straighteningHomotopy {n : ℕ} (simplex : RawSingularSimplex s n)
    (h : SimplexFitsConvexDomain D.domain simplex) : simplex.Homotopy (D.straighten simplex h) where
  toFun z := D.retract ⟨simplexVertexInterpolation simplex z, simplexVertexInterpolation_mem_domain h z⟩
  continuous_toFun := D.retract.continuous.comp
    ((simplexVertexInterpolation simplex).continuous.subtype_mk _)
  map_zero_left w := by
    calc
      _ = D.retract ⟨(simplex w).val, D.subset_domain (simplex w).property⟩ := by
        apply congrArg D.retract
        apply Subtype.ext
        change (1 - (0 : ℝ)) • (simplex w).val + (0 : ℝ) • simplexVertexAffine simplex w = _
        simp
      _ = _ := D.fixes (simplex w)
  map_one_left w := by
    change D.retract ⟨simplexVertexInterpolation simplex (1, w), _⟩ =
      D.retract ⟨simplexVertexAffine simplex w, _⟩
    apply congrArg D.retract
    apply Subtype.ext
    change (1 - (1 : ℝ)) • (simplex w).val + (1 : ℝ) • simplexVertexAffine simplex w = _
    simp

theorem straighten_precomp {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (simplex : RawSingularSimplex s b) (h : SimplexFitsConvexDomain D.domain simplex) :
    (D.straighten simplex h).comp (simplexMap f) =
      D.straighten (simplex.comp (simplexMap f)) (simplexFitsConvexDomain_precomp f h) := by
  apply ContinuousMap.ext
  intro w
  apply congrArg D.retract
  apply Subtype.ext
  exact ContinuousMap.congr_fun (simplexVertexAffine_precomp f simplex) w

theorem straighteningHomotopy_precomp {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1))
    (simplex : RawSingularSimplex s b) (h : SimplexFitsConvexDomain D.domain simplex)
    (t : unitInterval) (w : Simplex a) :
    D.straighteningHomotopy simplex h (t, simplexMap f w) =
      D.straighteningHomotopy (simplex.comp (simplexMap f)) (simplexFitsConvexDomain_precomp f h) (t, w) := by
  apply congrArg D.retract
  apply Subtype.ext
  change (1 - (t : ℝ)) • (simplex (simplexMap f w)).val +
      (t : ℝ) • simplexVertexAffine simplex (simplexMap f w) =
    (1 - (t : ℝ)) • (simplex (simplexMap f w)).val +
      (t : ℝ) • simplexVertexAffine (simplex.comp (simplexMap f)) w
  have ha : simplexVertexAffine simplex (simplexMap f w) =
      simplexVertexAffine (simplex.comp (simplexMap f)) w :=
    ContinuousMap.congr_fun (simplexVertexAffine_precomp f simplex) w
  rw [ha]

theorem exists_lipschitz_straighten {n : ℕ} (simplex : RawSingularSimplex s n)
    (h : SimplexFitsConvexDomain D.domain simplex) :
    ∃ L : ℝ≥0, LipschitzWith L (D.straighten simplex h) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_affineSingularSimplex
    (fun i => (simplex (stdSimplex.vertex i)).val)
  refine ⟨D.constant * L, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  have hr := D.lipschitz.dist_le_mul
    ⟨simplexVertexAffine simplex x, simplexVertexAffine_mem_domain h x⟩
    ⟨simplexVertexAffine simplex y, simplexVertexAffine_mem_domain h y⟩
  change dist (D.straighten simplex h x) (D.straighten simplex h y) ≤
    (D.constant : ℝ) * dist (simplexVertexAffine simplex x) (simplexVertexAffine simplex y) at hr
  exact hr.trans (by
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hL.dist_le_mul x y) D.constant.property)

theorem exists_lipschitz_straighteningHomotopy {n : ℕ} (simplex : RawSingularSimplex s n)
    (h : SimplexFitsConvexDomain D.domain simplex) {L : ℝ≥0} (hL : LipschitzWith L simplex) :
    ∃ K : ℝ≥0, LipschitzWith K (D.straighteningHomotopy simplex h).toContinuousMap := by
  obtain ⟨M, hM⟩ := exists_lipschitz_affineSingularSimplex
    (fun i => (simplex (stdSimplex.vertex i)).val)
  obtain ⟨K, hK⟩ := exists_lipschitz_unitInterval_interpolation
    (fun w => (simplex w).val) (simplexVertexAffine simplex)
    ((LipschitzWith.subtype_val s).comp hL) hM
  exact ⟨D.constant * K, D.lipschitz.comp
    (hK.subtype_mk (simplexVertexInterpolation_mem_domain h))⟩

end LipschitzNeighborhoodRetraction
end BanachIsometric.SingularPrism
