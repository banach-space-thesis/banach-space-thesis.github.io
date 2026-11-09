import BanachIsometric.SingularCrossReassociation

/-! The actual middle interchange of four spaces transports the
external homology products with the single Koszul sign. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open SingularAW

variable (A B C D : Type u)
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

def awProductInterchange : C((A × B) × (C × D), (A × C) × (B × D)) :=
  ⟨fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2)),
    ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))⟩

theorem rawHomologyCross_interchange {n p q r s : ℕ} (h : (p + q) + (r + s) = n)
    (a : RawHomology A p) (b : RawHomology B q) (c : RawHomology C r) (d : RawHomology D s) :
    rawFullHomologyMap (awProductInterchange A B C D) n
      (rawHomologyCross (A × B) (C × D) h (rawHomologyCross A B rfl a b) (rawHomologyCross C D rfl c d)) =
        (-1 : ℚ) ^ (q * r) • rawHomologyCross (A × C) (B × D) (by omega : (p + r) + (q + s) = n)
          (rawHomologyCross A C rfl a c) (rawHomologyCross B D rfl b d) := by
  let F₁ : C((A × B) × (C × D), A × (B × (C × D))) := awProductAssoc
  let F₂ : C(A × (B × (C × D)), A × ((B × C) × D)) :=
    awProductMap (ContinuousMap.id A) (awProductUnassoc B C D)
  let F₃ : C(A × ((B × C) × D), A × ((C × B) × D)) :=
    awProductMap (ContinuousMap.id A) (awProductMap (awProductSwap B C) (ContinuousMap.id D))
  let F₄ : C(A × ((C × B) × D), A × (C × (B × D))) :=
    awProductMap (ContinuousMap.id A) awProductAssoc
  let F₅ : C(A × (C × (B × D)), (A × C) × (B × D)) := awProductUnassoc A C (B × D)
  have hgeom : awProductInterchange A B C D = F₅.comp (F₄.comp (F₃.comp (F₂.comp F₁))) := rfl
  rw [hgeom]
  simp only [rawFullHomologyMap_apply_comp, F₁, F₂, F₃, F₄, F₅]
  rw [rawHomologyCross_associativity A B (C × D) h,
    rawHomologyCross_naturality (ContinuousMap.id A) (awProductUnassoc B C D),
    rawFullHomologyMap_id, LinearMap.id_apply,
    rawHomologyCross_unassociate B C D (rfl : q + r = q + r)
      (by omega : (q + r) + s = q + (r + s)) (rfl : r + s = r + s) rfl b c d,
    rawHomologyCross_naturality (ContinuousMap.id A)
      (awProductMap (awProductSwap B C) (ContinuousMap.id D)),
    rawFullHomologyMap_id, LinearMap.id_apply,
    rawHomologyCross_naturality (awProductSwap B C) (ContinuousMap.id D),
    rawFullHomologyMap_id, LinearMap.id_apply,
    rawHomologyCross_swap (n := q + r) (p := q) (q := r) rfl b c]
  simp only [map_smul, LinearMap.smul_apply]
  rw [rawHomologyCross_naturality (ContinuousMap.id A) (awProductAssoc (X := C) (Y := B) (Z := D)),
    rawFullHomologyMap_id, LinearMap.id_apply,
    rawHomologyCross_reassociate C B D (by omega : r + q = q + r)
      (by omega : (q + r) + s = q + (r + s)) (rfl : q + s = q + s)
      (by omega : r + (q + s) = q + (r + s)) c b d,
    rawHomologyCross_unassociate A C (B × D) (rfl : p + r = p + r)
      (by omega : (p + r) + (q + s) = n) (by omega : r + (q + s) = q + (r + s))
      (by omega : p + (q + (r + s)) = n) a c (rawHomologyCross B D rfl b d)]

end BanachIsometric.SingularEZ
