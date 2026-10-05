import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Bases
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-! Rich families of actual closed separable linear subspaces. The closure
of an increasing sequence is the ordinary topological closure of its union. -/
noncomputable section
open Set Topology TopologicalSpace
namespace ThesisCommon
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def richChainClosure (V : ℕ → Submodule 𝕜 E) : Submodule 𝕜 E :=
  (⨆ n, V n).topologicalClosure

theorem richChainClosure_coe (V : ℕ → Submodule 𝕜 E) (hV : Monotone V) :
    (richChainClosure V : Set E) = closure (⋃ n, (V n : Set E)) := by
  rw [richChainClosure, Submodule.topologicalClosure_coe,
    Submodule.coe_iSup_of_directed V hV.directed_le]

structure IsRichFamily (R : Set (Submodule 𝕜 E)) : Prop where
  closed : ∀ P ∈ R, IsClosed (P : Set E)
  separable : ∀ P ∈ R, IsSeparable (P : Set E)
  cofinal : ∀ M : Set E, IsSeparable M → ∃ P ∈ R, M ⊆ P
  closed_chain : ∀ V : ℕ → Submodule 𝕜 E, (∀ n, V n ∈ R) → Monotone V →
    richChainClosure V ∈ R

theorem IsRichFamily.iInter (R : ℕ → Set (Submodule 𝕜 E))
    (hR : ∀ n, IsRichFamily (R n)) : IsRichFamily (⋂ n, R n) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    exact (hR 0).closed P (mem_iInter.mp hP 0)
  · intro P hP
    exact (hR 0).separable P (mem_iInter.mp hP 0)
  · intro M hM
    obtain ⟨P₀, hP₀, hMP₀⟩ := (hR 0).cofinal M hM
    let S := {P : Submodule 𝕜 E // IsClosed (P : Set E) ∧ IsSeparable (P : Set E)}
    let start : S := ⟨P₀, (hR 0).closed P₀ hP₀, (hR 0).separable P₀ hP₀⟩
    have hstep : ∀ n : ℕ, ∀ P : S, ∃ Q : S,
        Q.val ∈ R (Nat.unpair n).1 ∧ P.val ≤ Q.val := by
      intro n P
      obtain ⟨Q, hQ, hPQ⟩ := (hR (Nat.unpair n).1).cofinal (P.val : Set E) P.property.2
      exact ⟨⟨Q, (hR _).closed Q hQ, (hR _).separable Q hQ⟩, hQ, hPQ⟩
    choose step hstep using hstep
    let V : ℕ → S := Nat.rec start (fun n P => step n P)
    have hsucc (n : ℕ) : (V (n + 1)).val ∈ R (Nat.unpair n).1 ∧
        (V n).val ≤ (V (n + 1)).val := hstep n (V n)
    have hmono : Monotone (fun n => (V n).val) :=
      monotone_nat_of_le_succ (fun n => (hsucc n).2)
    let C := richChainClosure (fun n => (V n).val)
    have hC (k : ℕ) : C ∈ R k := by
      let U : ℕ → Submodule 𝕜 E := fun n => (V (Nat.pair k n + 1)).val
      have hU (n : ℕ) : U n ∈ R k := by
        simpa only [U, Nat.unpair_pair] using (hsucc (Nat.pair k n)).1
      have hUmono : Monotone U := by
        intro a b hab
        change (V (Nat.pair k a + 1)).val ≤ (V (Nat.pair k b + 1)).val
        exact hmono (a := Nat.pair k a + 1) (b := Nat.pair k b + 1)
          (Nat.succ_le_succ
          ((show StrictMono (Nat.pair k) from fun _ _ h => Nat.pair_lt_pair_right k h).monotone hab))
      have heq : (⨆ n, (V n).val) = ⨆ n, U n := by
        apply le_antisymm
        · refine iSup_le fun n => ?_
          exact (hmono ((Nat.right_le_pair k n).trans (Nat.le_succ _))).trans (le_iSup U n)
        · exact iSup_le fun n => le_iSup (fun n => (V n).val) (Nat.pair k n + 1)
      change (⨆ n, (V n).val).topologicalClosure ∈ R k
      rw [heq]
      exact (hR k).closed_chain U hU hUmono
    refine ⟨C, mem_iInter.mpr hC, ?_⟩
    intro x hx
    exact ((le_iSup (fun n => (V n).val) 0).trans
      (Submodule.le_topologicalClosure _)) (hMP₀ hx)
  · intro V hV hmono
    exact mem_iInter.mpr fun n => (hR n).closed_chain V
      (fun k => mem_iInter.mp (hV k) n) hmono

end ThesisCommon
