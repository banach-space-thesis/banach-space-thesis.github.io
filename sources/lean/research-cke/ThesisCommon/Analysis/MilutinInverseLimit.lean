import ThesisCommon.Analysis.ContinuousMapPullback
import Mathlib.Topology.MetricSpace.PiNat

/-! The concrete sequential inverse limit underlying Ditor's averaging argument.
This module proves compactness and surjectivity of all coordinate projections,
without introducing an abstract limit object or assuming a lift exists. -/

noncomputable section
open Set
namespace ThesisCommon

theorem milutin_exists_compatible_sequence {K : ℕ → Type*}
    (φ : ∀ n, K (n + 1) → K n) (hφ : ∀ n, Function.Surjective (φ n))
    (k : ℕ) (x : K k) :
    ∃ z : ∀ n, K n, z k = x ∧ ∀ n, φ n (z (n + 1)) = z n := by
  induction k generalizing K with
  | zero =>
    let z : ∀ n, K n := fun n => Nat.rec x (fun n y => (hφ n y).choose) n
    refine ⟨z, rfl, ?_⟩
    intro n
    exact (hφ n (z n)).choose_spec
  | succ k ih =>
    obtain ⟨z, hzk, hz⟩ := ih (K := fun n => K (n + 1))
      (fun n => φ (n + 1)) (fun n => hφ (n + 1)) x
    let w : ∀ n, K n := fun n => Nat.casesOn n (φ 0 (z 0)) (fun m => z m)
    refine ⟨w, hzk, ?_⟩
    intro n
    cases n with
    | zero => rfl
    | succ n => exact hz n

variable {K : ℕ → Type*} [∀ n, TopologicalSpace (K n)]

def MilutinInverseLimit (φ : ∀ n, C(K (n + 1), K n)) :=
  { z : ∀ n, K n // ∀ n, φ n (z (n + 1)) = z n }

instance (φ : ∀ n, C(K (n + 1), K n)) : TopologicalSpace (MilutinInverseLimit φ) :=
  inferInstanceAs (TopologicalSpace { z : ∀ n, K n // ∀ n, φ n (z (n + 1)) = z n })

def milutinLimitProjection (φ : ∀ n, C(K (n + 1), K n)) (n : ℕ) :
    C(MilutinInverseLimit φ, K n) where
  toFun z := z.val n
  continuous_toFun := (continuous_apply n).comp continuous_subtype_val

@[simp] theorem milutinLimitProjection_apply (φ : ∀ n, C(K (n + 1), K n))
    (n : ℕ) (z : MilutinInverseLimit φ) : milutinLimitProjection φ n z = z.val n := rfl

theorem milutinLimitProjection_compatible (φ : ∀ n, C(K (n + 1), K n)) (n : ℕ) :
    (φ n).comp (milutinLimitProjection φ (n + 1)) = milutinLimitProjection φ n := by
  ext z
  exact z.property n

theorem milutinLimitProjection_surjective (φ : ∀ n, C(K (n + 1), K n))
    (hφ : ∀ n, Function.Surjective (φ n)) (n : ℕ) :
    Function.Surjective (milutinLimitProjection φ n) := by
  intro x
  obtain ⟨z, hzn, hz⟩ := milutin_exists_compatible_sequence (fun n => φ n) hφ n x
  exact ⟨⟨z, hz⟩, hzn⟩

theorem milutinInverseLimit_isClosed [∀ n, T2Space (K n)]
    (φ : ∀ n, C(K (n + 1), K n)) :
    IsClosed {z : ∀ n, K n | ∀ n, φ n (z (n + 1)) = z n} := by
  simp only [setOf_forall]
  exact isClosed_iInter fun n => isClosed_eq
    ((φ n).continuous.comp (continuous_apply (n + 1))) (continuous_apply n)

instance milutinInverseLimitCompactSpace [∀ n, CompactSpace (K n)] [∀ n, T2Space (K n)]
    (φ : ∀ n, C(K (n + 1), K n)) : CompactSpace (MilutinInverseLimit φ) :=
  isCompact_iff_compactSpace.mp (milutinInverseLimit_isClosed φ).isCompact

instance milutinInverseLimitT2Space [∀ n, T2Space (K n)]
    (φ : ∀ n, C(K (n + 1), K n)) : T2Space (MilutinInverseLimit φ) :=
  inferInstanceAs (T2Space { z : ∀ n, K n // ∀ n, φ n (z (n + 1)) = z n })

end ThesisCommon
