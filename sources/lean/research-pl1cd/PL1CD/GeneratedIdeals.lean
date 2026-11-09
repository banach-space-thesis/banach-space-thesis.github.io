import PL1CD.Statements
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
open scoped BigOperators

namespace PL1CD

variable (𝕜 : Type) [RCLike 𝕜]

abbrev SandwichData := ContinuumIndex × L1Operator 𝕜 × L1Operator 𝕜

def sandwichValue (P : ContinuumIndex → L1Operator 𝕜) (t : SandwichData 𝕜) :
    L1Operator 𝕜 := t.2.2.comp ((P t.1).comp t.2.1)

def HasFiniteSandwichSum (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) (T : L1Operator 𝕜) : Prop :=
  ∃ ts : List (SandwichData 𝕜), (∀ t ∈ ts, t.1 ∈ S) ∧
    T = (ts.map (sandwichValue 𝕜 P)).sum

theorem finiteSandwichSum_zero (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) : HasFiniteSandwichSum 𝕜 P S 0 :=
  ⟨[], by simp, by simp⟩

theorem finiteSandwichSum_add {P : ContinuumIndex → L1Operator 𝕜}
    {S : Set ContinuumIndex} {T W : L1Operator 𝕜}
    (hT : HasFiniteSandwichSum 𝕜 P S T) (hW : HasFiniteSandwichSum 𝕜 P S W) :
    HasFiniteSandwichSum 𝕜 P S (T + W) := by
  obtain ⟨ts, hts, rfl⟩ := hT
  obtain ⟨ws, hws, rfl⟩ := hW
  refine ⟨ts ++ ws, ?_, by simp⟩
  intro t ht
  exact (List.mem_append.mp ht).elim (hts t) (hws t)

theorem finiteSandwichSum_smul {P : ContinuumIndex → L1Operator 𝕜}
    {S : Set ContinuumIndex} {T : L1Operator 𝕜}
    (hT : HasFiniteSandwichSum 𝕜 P S T) (c : 𝕜) :
    HasFiniteSandwichSum 𝕜 P S (c • T) := by
  obtain ⟨ts, hts, rfl⟩ := hT
  refine ⟨ts.map (fun t => (t.1, t.2.1, c • t.2.2)), ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hts u hu
  · simp only [List.smul_sum, List.map_map, Function.comp_def,
      sandwichValue, ContinuousLinearMap.smul_comp]

def algebraicGeneratedIdeal (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) : Submodule 𝕜 (L1Operator 𝕜) where
  carrier := {T | HasFiniteSandwichSum 𝕜 P S T}
  zero_mem' := finiteSandwichSum_zero 𝕜 P S
  add_mem' := fun hT hW => finiteSandwichSum_add 𝕜 hT hW
  smul_mem' := fun c _T hT => finiteSandwichSum_smul 𝕜 hT c

theorem finiteSandwichSum_comp_left {P : ContinuumIndex → L1Operator 𝕜}
    {S : Set ContinuumIndex} {T : L1Operator 𝕜}
    (hT : HasFiniteSandwichSum 𝕜 P S T) (W : L1Operator 𝕜) :
    HasFiniteSandwichSum 𝕜 P S (W.comp T) := by
  obtain ⟨ts, hts, rfl⟩ := hT
  refine ⟨ts.map (fun t => (t.1, t.2.1, W.comp t.2.2)), ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hts u hu
  · change W * (ts.map (sandwichValue 𝕜 P)).sum = _
    rw [← List.sum_map_mul_left]
    simp only [List.map_map, Function.comp_def, sandwichValue]
    rfl

theorem finiteSandwichSum_comp_right {P : ContinuumIndex → L1Operator 𝕜}
    {S : Set ContinuumIndex} {T : L1Operator 𝕜}
    (hT : HasFiniteSandwichSum 𝕜 P S T) (W : L1Operator 𝕜) :
    HasFiniteSandwichSum 𝕜 P S (T.comp W) := by
  obtain ⟨ts, hts, rfl⟩ := hT
  refine ⟨ts.map (fun t => (t.1, t.2.1.comp W, t.2.2)), ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hts u hu
  · change (ts.map (sandwichValue 𝕜 P)).sum * W = _
    rw [← List.sum_map_mul_right]
    simp only [List.map_map, Function.comp_def, sandwichValue]
    rfl

theorem finiteSandwichSum_iff_fin (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) (T : L1Operator 𝕜) :
    HasFiniteSandwichSum 𝕜 P S T ↔
      ∃ n : ℕ, ∃ a : Fin n → ContinuumIndex, (∀ j, a j ∈ S) ∧
        ∃ U V : Fin n → L1Operator 𝕜,
          T = ∑ j, (V j).comp ((P (a j)).comp (U j)) := by
  constructor
  · rintro ⟨ts, hts, hT⟩
    refine ⟨ts.length, fun j => (ts.get j).1,
      fun j => hts _ (List.get_mem _ _),
      fun j => (ts.get j).2.1, fun j => (ts.get j).2.2, ?_⟩
    rw [hT]
    calc
      (ts.map (sandwichValue 𝕜 P)).sum =
          ((List.ofFn ts.get).map (sandwichValue 𝕜 P)).sum := by rw [List.ofFn_get]
      _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl
  · rintro ⟨n, a, ha, U, V, hT⟩
    refine ⟨List.ofFn (fun j => (a j, U j, V j)), ?_, ?_⟩
    · intro t ht
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht
      exact ha j
    · rw [List.map_ofFn, List.sum_ofFn]
      exact hT

def generatedIdeal (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) : Submodule 𝕜 (L1Operator 𝕜) :=
  (algebraicGeneratedIdeal 𝕜 P S).topologicalClosure

theorem coe_generatedIdeal (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) :
    (generatedIdeal 𝕜 P S : Set (L1Operator 𝕜)) = closedIdealGeneratedBy 𝕜 P S := by
  rw [generatedIdeal, Submodule.topologicalClosure_coe]
  unfold closedIdealGeneratedBy
  congr 1
  ext T
  exact finiteSandwichSum_iff_fin 𝕜 P S T

theorem generatedIdeal_isClosedTwoSided (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) : IsNormClosedTwoSidedIdeal 𝕜 (generatedIdeal 𝕜 P S) := by
  refine ⟨Submodule.isClosed_topologicalClosure _, ?_⟩
  intro T hT W
  change T ∈ closure (algebraicGeneratedIdeal 𝕜 P S : Set (L1Operator 𝕜)) at hT
  constructor
  · exact map_mem_closure (f := fun A : L1Operator 𝕜 => W * A)
      (continuous_const.mul continuous_id) hT
      (fun A hA => finiteSandwichSum_comp_left 𝕜 hA W)
  · exact map_mem_closure (f := fun A : L1Operator 𝕜 => A * W)
      (continuous_id.mul continuous_const) hT
      (fun A hA => finiteSandwichSum_comp_right 𝕜 hA W)

theorem generator_mem_generatedIdeal (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) {a : ContinuumIndex} (ha : a ∈ S) :
    P a ∈ generatedIdeal 𝕜 P S := by
  apply Submodule.le_topologicalClosure
  exact ⟨[(a, ContinuousLinearMap.id 𝕜 _, ContinuousLinearMap.id 𝕜 _)],
    by simpa using ha, by simp [sandwichValue]⟩

theorem generatedIdeal_le (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) (I : Submodule 𝕜 (L1Operator 𝕜))
    (hI : IsNormClosedTwoSidedIdeal 𝕜 I) (hP : ∀ a ∈ S, P a ∈ I) :
    generatedIdeal 𝕜 P S ≤ I := by
  apply Submodule.topologicalClosure_minimal _ ?_ hI.1
  intro T hT
  obtain ⟨ts, hts, rfl⟩ := hT
  induction ts with
  | nil => simpa using I.zero_mem
  | cons t ts ih =>
      rw [List.map_cons, List.sum_cons]
      apply I.add_mem
      · exact (hI.2 _ ((hI.2 _ (hP t.1 (hts t (by simp))) t.2.1).2) t.2.2).1
      · exact ih (fun u hu => hts u (by simp [hu]))

theorem generatedIdeal_le_iff (P : ContinuumIndex → L1Operator 𝕜)
    (S : Set ContinuumIndex) (I : Submodule 𝕜 (L1Operator 𝕜))
    (hI : IsNormClosedTwoSidedIdeal 𝕜 I) :
    generatedIdeal 𝕜 P S ≤ I ↔ ∀ a ∈ S, P a ∈ I :=
  ⟨fun h _a ha => h (generator_mem_generatedIdeal 𝕜 P S ha),
    generatedIdeal_le 𝕜 P S I hI⟩

theorem generatedIdeal_mono (P : ContinuumIndex → L1Operator 𝕜)
    {S T : Set ContinuumIndex} (h : S ⊆ T) :
    generatedIdeal 𝕜 P S ≤ generatedIdeal 𝕜 P T :=
  generatedIdeal_le 𝕜 P S _ (generatedIdeal_isClosedTwoSided 𝕜 P T)
    (fun _a ha => generator_mem_generatedIdeal 𝕜 P T (h ha))

theorem generatedIdeal_empty (P : ContinuumIndex → L1Operator 𝕜) :
    generatedIdeal 𝕜 P ∅ = ⊥ := by
  apply le_antisymm _ bot_le
  apply generatedIdeal_le 𝕜 P ∅ ⊥
  · refine ⟨?_, ?_⟩
    · simpa only [Submodule.bot_coe] using
        (isClosed_singleton : IsClosed ({0} : Set (L1Operator 𝕜)))
    · intro T hT U
      have hzero : T = 0 := by simpa using hT
      simp [hzero]
  · simp

end PL1CD
