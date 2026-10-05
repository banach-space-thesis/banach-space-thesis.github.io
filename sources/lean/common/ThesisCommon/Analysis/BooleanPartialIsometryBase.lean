import ThesisCommon.Analysis.BooleanPartialIsometryCardinality

noncomputable section
open Set
namespace ThesisCommon.BooleanPartialIsometry
variable {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]
  [MetricSpace A] [MetricSpace B]

def initial (h : dist (⊥ : A) ⊤ = dist (⊥ : B) ⊤) : BooleanPartialIsometry A B where
  graph := ⊥
  dist_eq := by
    rintro p (rfl | rfl) q (rfl | rfl)
    · simp
    · exact h
    · simpa only [dist_comm] using h
    · simp

theorem initial_source_finite (h : dist (⊥ : A) ⊤ = dist (⊥ : B) ⊤) :
    ((initial h).source : Set A).Finite := by
  apply (Set.toFinite ({(⊥ : A), ⊤} : Set A)).subset
  rintro a ⟨b, hab | hab⟩
  · have ha : a = ⊥ := congrArg Prod.fst hab
    simp [ha]
  · have ha : a = ⊤ := congrArg Prod.fst hab
    simp [ha]

def symm (p : BooleanPartialIsometry A B) : BooleanPartialIsometry B A where
  graph :=
    { carrier := {z | z.swap ∈ p.graph}
      bot_mem' := p.graph.bot_mem
      compl_mem' := p.graph.compl_mem
      infClosed' := fun z hz w hw => p.graph.inf_mem hz hw
      supClosed' := fun z hz w hw => p.graph.sup_mem hz hw }
  dist_eq := fun z hz w hw => (p.dist_eq _ hz _ hw).symm

theorem symm_source (p : BooleanPartialIsometry A B) : p.symm.source = p.target := rfl

theorem symm_target (p : BooleanPartialIsometry A B) : p.symm.target = p.source := rfl

theorem symm_symm (p : BooleanPartialIsometry A B) : p.symm.symm = p := by
  apply ext
  rfl

theorem symm_mono {p q : BooleanPartialIsometry A B} (h : p ≤ q) : p.symm ≤ q.symm :=
  fun _ hz => h hz

end ThesisCommon.BooleanPartialIsometry
