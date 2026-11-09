import ThesisCommon.Analysis.MilutinCompactCoding

/-! Encode the finite component labels into the actual binary Cantor space.
Each finite natural number is represented by its initial-segment indicator,
and the pairs of bit indices are enumerated by Nat.pair. -/

noncomputable section
namespace ThesisCommon

def milutinFiniteProductBinaryCode (d : ℕ → ℕ) : C((∀ n, Fin (d n)), ℕ → Bool) where
  toFun x k := decide ((Nat.unpair k).2 < (x (Nat.unpair k).1).val)
  continuous_toFun := continuous_pi fun k =>
    (continuous_of_discreteTopology (f := fun a : Fin (d (Nat.unpair k).1) =>
      decide ((Nat.unpair k).2 < a.val))).comp (continuous_apply (Nat.unpair k).1)

theorem milutinFiniteProductBinaryCode_injective (d : ℕ → ℕ) :
    Function.Injective (milutinFiniteProductBinaryCode d) := by
  intro x y hxy
  funext n
  apply Fin.ext
  have hcut (k : ℕ) : (k < (x n).val) ↔ (k < (y n).val) := by
    let a : ℕ → ℕ := fun i => (x i).val
    let b : ℕ → ℕ := fun i => (y i).val
    have h := congrFun hxy (Nat.pair n k)
    change decide ((Nat.unpair (Nat.pair n k)).2 < a (Nat.unpair (Nat.pair n k)).1) =
      decide ((Nat.unpair (Nat.pair n k)).2 < b (Nat.unpair (Nat.pair n k)).1) at h
    rw [Nat.unpair_pair] at h
    exact decide_eq_decide.mp h
  have hx := hcut (x n).val
  have hy := hcut (y n).val
  omega

def milutinCompactBinaryCode (B : MilutinCompactMetric) : C(MilutinCompactLimit B, ℕ → Bool) :=
  (milutinFiniteProductBinaryCode fun n => (milutinCompactCover B n).count).comp
    (milutinCompactCode B)

theorem milutinCompactBinaryCode_injective (B : MilutinCompactMetric) :
    Function.Injective (milutinCompactBinaryCode B) :=
  (milutinFiniteProductBinaryCode_injective _).comp (milutinCompactCode_injective B)

theorem milutinCompactBinaryCode_isClosedEmbedding (B : MilutinCompactMetric) :
    Topology.IsClosedEmbedding (milutinCompactBinaryCode B) :=
  (milutinCompactBinaryCode B).continuous.isClosedEmbedding (milutinCompactBinaryCode_injective B)

end ThesisCommon
