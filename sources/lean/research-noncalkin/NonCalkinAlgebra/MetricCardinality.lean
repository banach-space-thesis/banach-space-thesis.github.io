import NonCalkinAlgebra.Statements
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Cardinality

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open Filter Topology

/-- A point in the closure is encoded by a sequence in the original set.
This gives the cardinal bound without a separability assumption. -/
theorem cardinal_closure_le_sequences {E : Type} [MetricSpace E] (S : Set E) :
    Cardinal.mk (closure S) ≤ (Cardinal.mk S) ^ Cardinal.aleph0 := by
  classical
  have hex : ∀ x : closure S, ∃ f : ℕ → E,
      (∀ n : ℕ, f n ∈ S) ∧ Tendsto f atTop (𝓝 x.val) :=
    fun x => mem_closure_iff_seq_limit.mp x.property
  choose f hf hlim using hex
  let F : closure S → (ℕ → S) := fun x n => ⟨f x n, hf x n⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    have hseq : f x = f y := by
      funext n
      exact congrArg Subtype.val (congrFun hxy n)
    apply Subtype.ext
    have hy : Tendsto (f x) atTop (𝓝 y.val) := by rw [hseq]; exact hlim y
    exact tendsto_nhds_unique (hlim x) hy
  have h := Cardinal.mk_le_of_injective hinj
  simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_nat] using h

theorem cardinal_le_continuum_of_density_continuum {E : Type} [MetricSpace E]
    (hE : HasDensityCharacter E Cardinal.continuum) : Cardinal.mk E ≤ Cardinal.continuum := by
  obtain ⟨S, hS, hcard⟩ := hE.1
  have h := cardinal_closure_le_sequences S
  simpa only [hS.closure_eq, Cardinal.mk_univ, hcard, Cardinal.continuum_power_aleph0] using h

theorem cardinal_closure_le_continuum {E : Type} [MetricSpace E] (S : Set E)
    (hS : Cardinal.mk S ≤ Cardinal.continuum) :
    Cardinal.mk (closure S) ≤ Cardinal.continuum := by
  calc
    Cardinal.mk (closure S) ≤ (Cardinal.mk S) ^ Cardinal.aleph0 :=
      cardinal_closure_le_sequences S
    _ ≤ Cardinal.continuum ^ Cardinal.aleph0 := Cardinal.power_le_power_right hS
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0

theorem cardinal_prod_le_continuum {E F : Type}
    (hE : Cardinal.mk E ≤ Cardinal.continuum) (hF : Cardinal.mk F ≤ Cardinal.continuum) :
    Cardinal.mk (E × F) ≤ Cardinal.continuum := by
  calc
    Cardinal.mk (E × F) = Cardinal.mk E * Cardinal.mk F := by
      simp only [Cardinal.mk_prod, Cardinal.lift_id]
    _ ≤ Cardinal.continuum * Cardinal.continuum := mul_le_mul' hE hF
    _ = Cardinal.continuum := Cardinal.continuum_mul_self

end NonCalkinAlgebra
