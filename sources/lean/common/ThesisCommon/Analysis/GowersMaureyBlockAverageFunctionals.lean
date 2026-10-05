import ThesisCommon.Analysis.GowersMaureyCombinedAverages
import ThesisCommon.Analysis.GowersMaureySubspaceNPairs
import Mathlib.Logic.Equiv.Fin.Basic

/-! The combined functional for a rectangular family of actual RIS
averages. Flattening preserves the source successive order and gives the
checked dual norm bound two when the number of blocks does not exceed N. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem successive_flatten_blocks {k N : ℕ} (a : Fin k → Fin N → C00 𝕜)
    (ha : ∀ i, Successive (a i))
    (hab : ∀ i j, i < j → ∀ s t, Before (a i s) (a j t)) :
    Successive (fun i : Fin (k*N) => a i.divNat i.modNat) := by
  intro i j hij
  have hdiv : i.divNat ≤ j.divNat := Nat.div_le_div_right (Nat.le_of_lt hij)
  rcases lt_or_eq_of_le hdiv with h | h
  · exact hab _ _ h _ _
  · have hm : i.modNat < j.modNat := by
      have he : i.val / N = j.val / N := congrArg Fin.val h
      have hi := Nat.mod_add_div i.val N
      have hj := Nat.mod_add_div j.val N
      change i.val % N < j.val % N
      change i.val < j.val at hij
      rw [he] at hi
      omega
    change Before (a i.divNat i.modNat) (a j.divNat j.modNat)
    rw [h]
    exact ha _ _ _ hm

theorem sum_flatten_blocks {E : Type*} [AddCommMonoid E] {k N : ℕ}
    (a : Fin k → Fin N → E) :
    (∑ i : Fin (k*N), a i.divNat i.modNat) = ∑ i, ∑ n, a i n := by
  have he := Equiv.sum_comp (finProdFinEquiv : Fin k × Fin N ≃ Fin (k*N))
    (fun i : Fin (k*N) => a i.divNat i.modNat)
  have hi (p : Fin k × Fin N) :
      a (finProdFinEquiv p).divNat (finProdFinEquiv p).modNat = a p.1 p.2 := by
    have h := finProdFinEquiv.symm_apply_apply p
    exact congrArg (fun q : Fin k × Fin N => a q.1 q.2) h
  simpa only [hi,Fintype.sum_prod_type] using he.symm

theorem sum_averagedPairFunctional_eq {k N : ℕ} (a : Fin k → Fin N → C00 𝕜) :
    (∑ i, averagedPairFunctional (a i)) =
      (logarithmicWeight N)⁻¹ • ∑ i : Fin (k*N), a i.divNat i.modNat := by
  rw [sum_flatten_blocks]
  simp only [averagedPairFunctional,Finset.smul_sum]

theorem norm_sum_averagedPairing_le_two (D : ConstructionData 𝕜)
    {k N : ℕ} (hN : 0 < N) (hk : k ≤ N) (a : Fin k → Fin N → C00 𝕜)
    (ha : ∀ i, Successive (a i))
    (hab : ∀ i j, i < j → ∀ s t, Before (a i s) (a j t))
    (hunit : ∀ i n, DualUnit (implicitNorm D) (a i n)) :
    ‖∑ i, completedPairing D (averagedPairFunctional (a i))‖ ≤ 2 := by
  rw [← map_sum,sum_averagedPairFunctional_eq]
  exact norm_combined_average_completedPairing_le_two D hN hk _
    (successive_flatten_blocks a ha hab) (fun i => hunit _ _)

end ThesisCommon.GowersMaurey
