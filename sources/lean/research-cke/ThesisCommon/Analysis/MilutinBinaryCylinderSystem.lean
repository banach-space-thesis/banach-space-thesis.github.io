import ThesisCommon.Analysis.MilutinAveragingExtension
import ThesisCommon.Analysis.ContinuousMapPullback
import Mathlib.Data.Fin.Tuple.Basic

/-! The finite-prefix inverse system for the actual binary Cantor space. -/

noncomputable section
namespace ThesisCommon

abbrev MilutinBinaryWord (n : ℕ) := Fin n → Bool

def milutinBinaryWordBonding (n : ℕ) :
    C(MilutinBinaryWord (n + 1), MilutinBinaryWord n) :=
  ⟨Fin.init, continuous_of_discreteTopology⟩

theorem milutinBinaryWordBonding_surjective (n : ℕ) :
    Function.Surjective (milutinBinaryWordBonding n) := by
  intro w
  refine ⟨Fin.snoc w false, ?_⟩
  ext i
  exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => Bool) false w i

def milutinBinaryWordPrefix (n : ℕ) : C((ℕ → Bool), MilutinBinaryWord n) :=
  ⟨fun x i => x i.val, continuous_pi fun i => continuous_apply i.val⟩

@[simp] theorem milutinBinaryWordPrefix_init (n : ℕ) (x : ℕ → Bool) :
    Fin.init (milutinBinaryWordPrefix (n + 1) x) = milutinBinaryWordPrefix n x := rfl

theorem milutinBinaryWordPrefix_snoc (n : ℕ) (x : ℕ → Bool) :
    milutinBinaryWordPrefix (n + 1) x = Fin.snoc (milutinBinaryWordPrefix n x) (x n) := by
  rw [← Fin.snoc_init_self (milutinBinaryWordPrefix (n + 1) x)]
  rfl

def milutinBinaryToWordLimit : C((ℕ → Bool), MilutinInverseLimit milutinBinaryWordBonding) :=
  ⟨fun x => ⟨fun n => milutinBinaryWordPrefix n x, fun _ => rfl⟩,
    (continuous_pi fun n => (milutinBinaryWordPrefix n).continuous).subtype_mk _⟩

def milutinWordLimitToBinary : C(MilutinInverseLimit milutinBinaryWordBonding, (ℕ → Bool)) :=
  ⟨fun z n => z.val (n + 1) (Fin.last n), continuous_pi fun n =>
    (continuous_apply (Fin.last n)).comp (milutinLimitProjection milutinBinaryWordBonding
      (n + 1)).continuous⟩

@[simp] theorem milutinWordLimitToBinary_toWordLimit (x : ℕ → Bool) :
    milutinWordLimitToBinary (milutinBinaryToWordLimit x) = x := rfl

@[simp] theorem milutinBinaryToWordLimit_projection (n : ℕ) (x : ℕ → Bool) :
    milutinLimitProjection milutinBinaryWordBonding n (milutinBinaryToWordLimit x) =
      milutinBinaryWordPrefix n x := rfl

theorem milutinBinaryWord_sum_snoc {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : MilutinBinaryWord (n + 1) → M) :
    ∑ w, f w = ∑ w : MilutinBinaryWord n, (f (Fin.snoc w false) + f (Fin.snoc w true)) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply, Fintype.sum_bool, Finset.sum_add_distrib]
  exact add_comm _ _

end ThesisCommon
