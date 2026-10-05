import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen
import Mathlib.Topology.Separation.Hausdorff

/-! The compact space of Boolean-valued homomorphisms of an arbitrary
Boolean algebra. No countability or nontriviality assumption is imposed. -/
noncomputable section
open Set TopologicalSpace
namespace ThesisCommon
variable {B : Type*} [BooleanAlgebra B]

def IsBooleanStonePoint (f : B → Bool) : Prop :=
  f ⊥ = false ∧ f ⊤ = true ∧ (∀ a b, f (a ⊓ b) = f a ⊓ f b) ∧
    ∀ a b, f (a ⊔ b) = f a ⊔ f b

def BooleanStonePoint (B : Type*) [BooleanAlgebra B] := {f : B → Bool // IsBooleanStonePoint f}

instance booleanStonePointTopology : TopologicalSpace (BooleanStonePoint B) :=
  inferInstanceAs (TopologicalSpace {f : B → Bool // IsBooleanStonePoint f})

instance booleanStonePointT2 : T2Space (BooleanStonePoint B) :=
  inferInstanceAs (T2Space {f : B → Bool // IsBooleanStonePoint f})

theorem isClosed_booleanStonePoints : IsClosed {f : B → Bool | IsBooleanStonePoint f} := by
  have hinf : IsClosed {f : B → Bool | ∀ a b, f (a ⊓ b) = f a ⊓ f b} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro b
    have hc : Continuous (fun f : B → Bool => (f a, f b)) :=
      (continuous_apply a).prodMk (continuous_apply b)
    have hf : Continuous (fun z : Bool × Bool => z.1 ⊓ z.2) := continuous_of_discreteTopology
    exact isClosed_eq (continuous_apply _) (hf.comp hc)
  have hsup : IsClosed {f : B → Bool | ∀ a b, f (a ⊔ b) = f a ⊔ f b} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro b
    have hc : Continuous (fun f : B → Bool => (f a, f b)) :=
      (continuous_apply a).prodMk (continuous_apply b)
    have hf : Continuous (fun z : Bool × Bool => z.1 ⊔ z.2) := continuous_of_discreteTopology
    exact isClosed_eq (continuous_apply _) (hf.comp hc)
  exact (isClosed_eq (continuous_apply ⊥) continuous_const).inter
    ((isClosed_eq (continuous_apply ⊤) continuous_const).inter (hinf.inter hsup))

instance booleanStonePointCompact : CompactSpace (BooleanStonePoint B) :=
  isCompact_iff_compactSpace.mp isClosed_booleanStonePoints.isCompact

def booleanStoneHom (p : BooleanStonePoint B) : BoundedLatticeHom B Bool where
  toFun := p.val
  map_bot' := p.property.1
  map_top' := p.property.2.1
  map_inf' := p.property.2.2.1
  map_sup' := p.property.2.2.2

theorem continuous_booleanStoneEval (a : B) :
    Continuous (fun p : BooleanStonePoint B => booleanStoneHom p a) :=
  (continuous_apply a).comp continuous_subtype_val

def booleanStoneSet (a : B) : Set (BooleanStonePoint B) := {p | booleanStoneHom p a = true}

theorem isClopen_booleanStoneSet (a : B) : IsClopen (booleanStoneSet a) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_booleanStoneEval a)

@[simp] theorem booleanStoneSet_bot : booleanStoneSet (⊥ : B) = ∅ := by
  ext p
  simp [booleanStoneSet]

@[simp] theorem booleanStoneSet_top : booleanStoneSet (⊤ : B) = univ := by
  ext p
  simp [booleanStoneSet]

@[simp] theorem booleanStoneSet_inf (a b : B) :
    booleanStoneSet (a ⊓ b) = booleanStoneSet a ∩ booleanStoneSet b := by
  ext p
  simp [booleanStoneSet]

@[simp] theorem booleanStoneSet_sup (a b : B) :
    booleanStoneSet (a ⊔ b) = booleanStoneSet a ∪ booleanStoneSet b := by
  ext p
  simp [booleanStoneSet]

@[simp] theorem booleanStoneSet_compl (a : B) :
    booleanStoneSet aᶜ = (booleanStoneSet a)ᶜ := by
  ext p
  simp [booleanStoneSet, map_compl']

end ThesisCommon
