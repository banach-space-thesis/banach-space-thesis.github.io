import ThesisCommon.Analysis.JamesStepDecomposition
import ThesisCommon.Analysis.JamesConstantPrefixes

/-! Every subsequence of the constant-prefix summing sequence is obtained
from it by an actual norm-one repetition map on James space. -/
noncomputable section
namespace ThesisCommon

theorem jamesStepIndex_le_iff (σ : ℕ → ℕ) (hσ : StrictMono σ) (hzero : σ 0 = 0)
    (m j : ℕ) : jamesStepIndex σ m ≤ j ↔ m < σ (j + 1) := by
  constructor
  · intro h
    by_contra hn
    have hh := jamesStepIndex_monotone σ (le_of_not_gt hn)
    rw [jamesStepIndex_at_endpoint σ hσ] at hh
    omega
  · intro h
    have hs : σ (jamesStepIndex σ m) ≤ m :=
      Nat.findGreatest_spec (P := fun j => σ j ≤ m) (Nat.zero_le m)
        (by simpa only [hzero] using Nat.zero_le m)
    by_contra hn
    have hi : j + 1 ≤ jamesStepIndex σ m := by omega
    have hh := hσ.monotone hi
    omega

def jamesPrefixEndpoints (β : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => β n + 1

theorem jamesPrefixEndpoints_strict (β : ℕ → ℕ) (hβ : StrictMono β) :
    StrictMono (jamesPrefixEndpoints β) := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp [jamesPrefixEndpoints]
  | succ n =>
    change β n + 1 < β (n + 1) + 1
    exact Nat.add_lt_add_right (hβ (Nat.lt_succ_self n)) 1

variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ⊤)
  (β : ℕ → ℕ) (hβ : StrictMono β)

def jamesPrefixRepeat : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  jamesRepeat p hp (jamesPrefixEndpoints β) (jamesPrefixEndpoints_strict β hβ)

theorem jamesPrefixRepeat_norm_le : ‖jamesPrefixRepeat (𝕜 := 𝕜) p hp β hβ‖ ≤ 1 :=
  jamesRepeat_norm_le p hp _ _

@[simp] theorem jamesPrefixRepeat_prefix (n : ℕ) :
    jamesPrefixRepeat (𝕜 := 𝕜) p hp β hβ (jamesConstantPrefix p hp n) =
      jamesConstantPrefix p hp (β n) := by
  ext k
  change jamesRepeat (𝕜 := 𝕜) p hp _ _ (jamesConstantPrefix p hp n) k = _
  rw [jamesRepeat_apply, jamesConstantPrefix_apply, jamesConstantPrefix_apply]
  simp only [jamesStepIndex_le_iff (jamesPrefixEndpoints β)
    (jamesPrefixEndpoints_strict β hβ) rfl, jamesPrefixEndpoints, Nat.lt_succ_iff]

end ThesisCommon
