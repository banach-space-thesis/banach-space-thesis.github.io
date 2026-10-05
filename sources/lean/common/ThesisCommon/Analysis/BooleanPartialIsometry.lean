import ThesisCommon.Analysis.DenseBooleanIsometryExtension
import Mathlib.Order.Zorn

/-! Compatible partial Boolean isometries, represented by their actual graphs.
Nonempty chains have unions without introducing choices of incompatible maps. -/
noncomputable section
open Set
namespace ThesisCommon
variable {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]
  [MetricSpace A] [MetricSpace B]

structure BooleanPartialIsometry (A B : Type*) [BooleanAlgebra A] [BooleanAlgebra B]
    [MetricSpace A] [MetricSpace B] where
  graph : BooleanSubalgebra (A × B)
  dist_eq : ∀ p ∈ graph, ∀ q ∈ graph, dist p.1 q.1 = dist p.2 q.2

namespace BooleanPartialIsometry

@[ext] theorem ext {p q : BooleanPartialIsometry A B} (h : p.graph = q.graph) : p = q := by
  cases p
  cases q
  cases h
  rfl

instance booleanPartialIsometryPartialOrder : PartialOrder (BooleanPartialIsometry A B) :=
  PartialOrder.lift graph (fun _ _ => ext)

theorem le_def (p q : BooleanPartialIsometry A B) : p ≤ q ↔ p.graph ≤ q.graph := Iff.rfl

def source (p : BooleanPartialIsometry A B) : BooleanSubalgebra A where
  carrier := {a | ∃ b, (a,b) ∈ p.graph}
  bot_mem' := ⟨⊥, p.graph.bot_mem⟩
  compl_mem' := by
    rintro a ⟨b, hb⟩
    exact ⟨bᶜ, p.graph.compl_mem hb⟩
  infClosed' := by
    rintro a ⟨b, hb⟩ c ⟨d, hd⟩
    exact ⟨b ⊓ d, p.graph.inf_mem hb hd⟩
  supClosed' := by
    rintro a ⟨b, hb⟩ c ⟨d, hd⟩
    exact ⟨b ⊔ d, p.graph.sup_mem hb hd⟩

def target (p : BooleanPartialIsometry A B) : BooleanSubalgebra B where
  carrier := {b | ∃ a, (a,b) ∈ p.graph}
  bot_mem' := ⟨⊥, p.graph.bot_mem⟩
  compl_mem' := by
    rintro b ⟨a, ha⟩
    exact ⟨aᶜ, p.graph.compl_mem ha⟩
  infClosed' := by
    rintro b ⟨a, ha⟩ d ⟨c, hc⟩
    exact ⟨a ⊓ c, p.graph.inf_mem ha hc⟩
  supClosed' := by
    rintro b ⟨a, ha⟩ d ⟨c, hc⟩
    exact ⟨a ⊔ c, p.graph.sup_mem ha hc⟩

theorem right_unique (p : BooleanPartialIsometry A B) {a : A} {b c : B}
    (hb : (a,b) ∈ p.graph) (hc : (a,c) ∈ p.graph) : b = c := by
  have h := p.dist_eq _ hb _ hc
  simpa only [dist_self, eq_comm, dist_eq_zero] using h

theorem left_unique (p : BooleanPartialIsometry A B) {a c : A} {b : B}
    (ha : (a,b) ∈ p.graph) (hc : (c,b) ∈ p.graph) : a = c := by
  have h := p.dist_eq _ ha _ hc
  simpa only [dist_self, dist_eq_zero] using h

def value (p : BooleanPartialIsometry A B) (a : p.source) : p.target :=
  ⟨a.property.choose, ⟨a.val, a.property.choose_spec⟩⟩

theorem value_mem (p : BooleanPartialIsometry A B) (a : p.source) :
    (a.val, (p.value a).val) ∈ p.graph := a.property.choose_spec

theorem value_injective (p : BooleanPartialIsometry A B) : Function.Injective p.value := by
  intro a c hac
  apply Subtype.ext
  have h := p.value_mem c
  rw [← hac] at h
  exact p.left_unique (p.value_mem a) h

theorem value_surjective (p : BooleanPartialIsometry A B) : Function.Surjective p.value := by
  intro b
  obtain ⟨a, ha⟩ := b.property
  refine ⟨⟨a, b.val, ha⟩, ?_⟩
  apply Subtype.ext
  exact p.right_unique (p.value_mem _) ha

theorem value_inf (p : BooleanPartialIsometry A B) (a c : p.source) :
    p.value (a ⊓ c) = p.value a ⊓ p.value c := by
  apply Subtype.ext
  exact p.right_unique (p.value_mem _) (p.graph.inf_mem (p.value_mem a) (p.value_mem c))

def orderIso (p : BooleanPartialIsometry A B) : p.source ≃o p.target where
  toEquiv := Equiv.ofBijective p.value ⟨p.value_injective, p.value_surjective⟩
  map_rel_iff' := by
    intro a c
    change p.value a ≤ p.value c ↔ a ≤ c
    rw [← inf_eq_left, ← p.value_inf, p.value_injective.eq_iff, inf_eq_left]

theorem orderIso_isometry (p : BooleanPartialIsometry A B) : Isometry p.orderIso := by
  apply Isometry.of_dist_eq
  intro a c
  exact (p.dist_eq _ (p.value_mem a) _ (p.value_mem c)).symm

theorem source_mono {p q : BooleanPartialIsometry A B} (h : p ≤ q) : p.source ≤ q.source := by
  rintro a ⟨b, hb⟩
  exact ⟨b, h hb⟩

theorem target_mono {p q : BooleanPartialIsometry A B} (h : p ≤ q) : p.target ≤ q.target := by
  rintro b ⟨a, ha⟩
  exact ⟨a, h ha⟩

def chainUnion (c : Set (BooleanPartialIsometry A B)) (hc : c.Nonempty)
    (hchain : IsChain (· ≤ ·) c) : BooleanPartialIsometry A B where
  graph :=
    { carrier := {z | ∃ p ∈ c, z ∈ p.graph}
      bot_mem' := ⟨hc.choose, hc.choose_spec, hc.choose.graph.bot_mem⟩
      compl_mem' := by
        rintro z ⟨p, hp, hz⟩
        exact ⟨p, hp, p.graph.compl_mem hz⟩
      infClosed' := by
        rintro z ⟨p, hp, hz⟩ w ⟨q, hq, hw⟩
        obtain ⟨r, hr, hpr, hqr⟩ := hchain.directedOn p hp q hq
        exact ⟨r, hr, r.graph.inf_mem (hpr hz) (hqr hw)⟩
      supClosed' := by
        rintro z ⟨p, hp, hz⟩ w ⟨q, hq, hw⟩
        obtain ⟨r, hr, hpr, hqr⟩ := hchain.directedOn p hp q hq
        exact ⟨r, hr, r.graph.sup_mem (hpr hz) (hqr hw)⟩ }
  dist_eq := by
    rintro z ⟨p, hp, hz⟩ w ⟨q, hq, hw⟩
    obtain ⟨r, hr, hpr, hqr⟩ := hchain.directedOn p hp q hq
    exact r.dist_eq z (hpr hz) w (hqr hw)

theorem le_chainUnion (c : Set (BooleanPartialIsometry A B)) (hc : c.Nonempty)
    (hchain : IsChain (· ≤ ·) c) {p : BooleanPartialIsometry A B} (hp : p ∈ c) :
    p ≤ chainUnion c hc hchain := fun _ hz => ⟨p, hp, hz⟩

theorem chainUnion_le (c : Set (BooleanPartialIsometry A B)) (hc : c.Nonempty)
    (hchain : IsChain (· ≤ ·) c) {q : BooleanPartialIsometry A B}
    (hq : ∀ p ∈ c, p ≤ q) : chainUnion c hc hchain ≤ q := by
  rintro z ⟨p, hp, hz⟩
  exact hq p hp hz

theorem exists_global_extension [CompleteSpace A] [CompleteSpace B]
    [ContinuousInf A] [ContinuousInf B] (p : BooleanPartialIsometry A B)
    (hs : Dense (p.source : Set A)) (ht : Dense (p.target : Set B)) :
    ∃ e : A ≃o B, Isometry e ∧ ∀ a : p.source, e a.val = (p.orderIso a).val :=
  exists_booleanOrderIso_extension_of_dense p.source p.target hs ht p.orderIso p.orderIso_isometry

end BooleanPartialIsometry
end ThesisCommon
