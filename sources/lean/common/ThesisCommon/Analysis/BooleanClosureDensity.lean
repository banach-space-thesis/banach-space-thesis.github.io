import ThesisCommon.Analysis.BooleanClosureCardinality
import ThesisCommon.Analysis.TopologicalDensity
import Mathlib.Topology.Order.Lattice

/-! The actual topological closure of a Boolean subalgebra, and bounds on
its density. These retain finite density at finitely generated stages. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon
universe u

theorem topologicalDensity_closure_le_card {X : Type u} [TopologicalSpace X] (s : Set X) :
    topologicalDensity (closure s) ≤ #s := by
  let j : s → closure s := Set.inclusion subset_closure
  have hj : DenseRange j := (denseRange_inclusion_iff subset_closure).mpr subset_rfl
  exact (topologicalDensity_le_card_of_dense hj).trans Cardinal.mk_range_le

variable {B : Type u} [BooleanAlgebra B] [TopologicalSpace B] [TopologicalLattice B]

def booleanSubalgebraTopologicalClosure (S : BooleanSubalgebra B)
    (hc : Continuous (fun a : B => aᶜ)) : BooleanSubalgebra B where
  carrier := closure (S : Set B)
  supClosed' := fun _ hx _ hy => map_mem_closure₂ continuous_sup hx hy (fun _ ha _ hb => S.sup_mem ha hb)
  infClosed' := fun _ hx _ hy => map_mem_closure₂ continuous_inf hx hy (fun _ ha _ hb => S.inf_mem ha hb)
  compl_mem' := fun hx => map_mem_closure hc hx (fun _ ha => S.compl_mem ha)
  bot_mem' := subset_closure S.bot_mem

theorem booleanSubalgebraTopologicalClosure_coe (S : BooleanSubalgebra B)
    (hc : Continuous (fun a : B => aᶜ)) :
    (booleanSubalgebraTopologicalClosure S hc : Set B) = closure (S : Set B) := rfl

theorem le_booleanSubalgebraTopologicalClosure (S : BooleanSubalgebra B)
    (hc : Continuous (fun a : B => aᶜ)) : S ≤ booleanSubalgebraTopologicalClosure S hc :=
  subset_closure

theorem isClosed_booleanSubalgebraTopologicalClosure (S : BooleanSubalgebra B)
    (hc : Continuous (fun a : B => aᶜ)) :
    IsClosed (booleanSubalgebraTopologicalClosure S hc : Set B) := isClosed_closure

theorem booleanSubalgebraTopologicalClosure_le_iff (S T : BooleanSubalgebra B)
    (hc : Continuous (fun a : B => aᶜ)) (hT : IsClosed (T : Set B)) :
    booleanSubalgebraTopologicalClosure S hc ≤ T ↔ S ≤ T := by
  exact ⟨fun h => (le_booleanSubalgebraTopologicalClosure S hc).trans h,
    fun h => closure_minimal h hT⟩

theorem topologicalDensity_booleanSubalgebraTopologicalClosure_le
    (S : BooleanSubalgebra B) (hc : Continuous (fun a : B => aᶜ)) :
    topologicalDensity (booleanSubalgebraTopologicalClosure S hc) ≤ #S :=
  topologicalDensity_closure_le_card (S : Set B)

theorem topologicalDensity_booleanGeneratedClosure_le_max
    (C : Set B) (hc : Continuous (fun a : B => aᶜ)) :
    topologicalDensity (booleanSubalgebraTopologicalClosure (BooleanSubalgebra.closure C) hc) ≤
      max ℵ₀ #C :=
  (topologicalDensity_booleanSubalgebraTopologicalClosure_le _ hc).trans
    (cardinal_booleanSubalgebraClosure_le_max C)

theorem topologicalDensity_booleanGeneratedClosure_lt_aleph0_of_finite
    {C : Set B} (hC : C.Finite) (hc : Continuous (fun a : B => aᶜ)) :
    topologicalDensity (booleanSubalgebraTopologicalClosure (BooleanSubalgebra.closure C) hc) < ℵ₀ :=
  (topologicalDensity_booleanSubalgebraTopologicalClosure_le _ hc).trans_lt
    (cardinal_booleanSubalgebraClosure_lt_aleph0 hC)

theorem topologicalDensity_booleanGeneratedClosure_lt
    (C : Set B) (hc : Continuous (fun a : B => aᶜ))
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hC : #C < κ) :
    topologicalDensity (booleanSubalgebraTopologicalClosure (BooleanSubalgebra.closure C) hc) < κ := by
  rcases eq_or_lt_of_le hκ with heq | hlt
  · subst κ
    exact topologicalDensity_booleanGeneratedClosure_lt_aleph0_of_finite
      (Cardinal.lt_aleph0_iff_set_finite.mp hC) hc
  · exact (topologicalDensity_booleanGeneratedClosure_le_max C hc).trans_lt (max_lt hlt hC)

end ThesisCommon
