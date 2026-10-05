import ThesisCommon.Analysis.BooleanPartialIsometry
import ThesisCommon.Analysis.BooleanClosureDensity

/-! Completion of a partial Boolean isometry by taking the actual closure
of its graph. Its two domains are exactly the closures of the original domains. -/
noncomputable section
open Set
namespace ThesisCommon.BooleanPartialIsometry
variable {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]
  [MetricSpace A] [MetricSpace B]

theorem orderIso_extension {p q : BooleanPartialIsometry A B} (h : p ≤ q) (a : p.source) :
    (q.orderIso ⟨a.val, source_mono h a.property⟩).val = (p.orderIso a).val :=
  q.right_unique (q.value_mem _) (h (p.value_mem a))

theorem isometry_fst (p : BooleanPartialIsometry A B) :
    Isometry (fun z : p.graph => z.val.1) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist z.val.1 w.val.1 = max (dist z.val.1 w.val.1) (dist z.val.2 w.val.2)
  rw [← p.dist_eq _ z.property _ w.property, max_self]

theorem isometry_snd (p : BooleanPartialIsometry A B) :
    Isometry (fun z : p.graph => z.val.2) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist z.val.2 w.val.2 = max (dist z.val.1 w.val.1) (dist z.val.2 w.val.2)
  rw [p.dist_eq _ z.property _ w.property, max_self]

theorem isClosed_source_of_graph [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) (hp : IsClosed (p.graph : Set (A × B))) :
    IsClosed (p.source : Set A) := by
  letI : CompleteSpace p.graph := hp.completeSpace_coe
  have heq : range (fun z : p.graph => z.val.1) = (p.source : Set A) := by
    ext a
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.val.2,z.property⟩
    · rintro ⟨b,hb⟩
      exact ⟨⟨(a,b),hb⟩,rfl⟩
  rw [← heq]
  exact p.isometry_fst.isClosedEmbedding.isClosed_range

theorem isClosed_target_of_graph [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) (hp : IsClosed (p.graph : Set (A × B))) :
    IsClosed (p.target : Set B) := by
  letI : CompleteSpace p.graph := hp.completeSpace_coe
  have heq : range (fun z : p.graph => z.val.2) = (p.target : Set B) := by
    ext b
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.val.1,z.property⟩
    · rintro ⟨a,ha⟩
      exact ⟨⟨(a,b),ha⟩,rfl⟩
  rw [← heq]
  exact p.isometry_snd.isClosedEmbedding.isClosed_range

variable [TopologicalLattice A] [TopologicalLattice B]
local instance booleanPartialProductTopologicalLattice : TopologicalLattice (A × B) where
  continuous_inf :=
    ((continuous_fst.fst.inf continuous_snd.fst).prodMk
      (continuous_fst.snd.inf continuous_snd.snd))
  continuous_sup :=
    ((continuous_fst.fst.sup continuous_snd.fst).prodMk
      (continuous_fst.snd.sup continuous_snd.snd))
variable (hA : Continuous (fun a : A => aᶜ)) (hB : Continuous (fun b : B => bᶜ))

def metricClosure (p : BooleanPartialIsometry A B) : BooleanPartialIsometry A B where
  graph := booleanSubalgebraTopologicalClosure p.graph
    ((hA.comp continuous_fst).prodMk (hB.comp continuous_snd))
  dist_eq := by
    intro x hx y hy
    have hfixed (y : A × B) (hy : y ∈ p.graph) :
        ∀ x ∈ closure (p.graph : Set (A × B)), dist x.1 y.1 = dist x.2 y.2 := by
      apply closure_minimal
      · intro x hx
        exact p.dist_eq x hx y hy
      · exact isClosed_eq (continuous_fst.dist continuous_const) (continuous_snd.dist continuous_const)
    have hclosed : IsClosed {y : A × B | dist x.1 y.1 = dist x.2 y.2} :=
      isClosed_eq (continuous_const.dist continuous_fst) (continuous_const.dist continuous_snd)
    exact closure_minimal (fun y hy => hfixed y hy x hx) hclosed hy

theorem le_metricClosure (p : BooleanPartialIsometry A B) : p ≤ p.metricClosure hA hB :=
  subset_closure

theorem metricClosure_graph (p : BooleanPartialIsometry A B) :
    ((p.metricClosure hA hB).graph : Set (A × B)) = closure (p.graph : Set (A × B)) := rfl

theorem metricClosure_source [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) :
    ((p.metricClosure hA hB).source : Set A) = closure (p.source : Set A) := by
  apply subset_antisymm
  · rintro a ⟨b,hb⟩
    have h : Prod.fst ⁻¹' closure (p.source : Set A) ⊇ closure (p.graph : Set (A × B)) :=
      closure_minimal (fun z hz => subset_closure ⟨z.2,hz⟩) (isClosed_closure.preimage continuous_fst)
    exact h hb
  · exact closure_minimal (source_mono (p.le_metricClosure hA hB))
      ((p.metricClosure hA hB).isClosed_source_of_graph isClosed_closure)

theorem metricClosure_target [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) :
    ((p.metricClosure hA hB).target : Set B) = closure (p.target : Set B) := by
  apply subset_antisymm
  · rintro b ⟨a,ha⟩
    have h : Prod.snd ⁻¹' closure (p.target : Set B) ⊇ closure (p.graph : Set (A × B)) :=
      closure_minimal (fun z hz => subset_closure ⟨z.1,hz⟩) (isClosed_closure.preimage continuous_snd)
    exact h ha
  · exact closure_minimal (target_mono (p.le_metricClosure hA hB))
      ((p.metricClosure hA hB).isClosed_target_of_graph isClosed_closure)

theorem isClosed_metricClosure_source [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) : IsClosed ((p.metricClosure hA hB).source : Set A) := by
  rw [metricClosure_source]
  exact isClosed_closure

theorem isClosed_metricClosure_target [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) : IsClosed ((p.metricClosure hA hB).target : Set B) := by
  rw [metricClosure_target]
  exact isClosed_closure

theorem density_metricClosure_source_le [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) :
    topologicalDensity (p.metricClosure hA hB).source ≤ Cardinal.mk p.source := by
  change topologicalDensity ((p.metricClosure hA hB).source : Set A) ≤ _
  rw [metricClosure_source]
  exact topologicalDensity_closure_le_card (p.source : Set A)

theorem density_metricClosure_target_le [CompleteSpace A] [CompleteSpace B]
    (p : BooleanPartialIsometry A B) :
    topologicalDensity (p.metricClosure hA hB).target ≤ Cardinal.mk p.target := by
  change topologicalDensity ((p.metricClosure hA hB).target : Set B) ≤ _
  rw [metricClosure_target]
  exact topologicalDensity_closure_le_card (p.target : Set B)

end ThesisCommon.BooleanPartialIsometry
