import BanachIsometric.RawSingularChains
import BanachIsometric.SingularPrismHomotopy
import BanachIsometric.PrismCancellation

/-! The actual rational singular prism operator and its chain-homotopy
identity. Every cancellation is discharged using the actual continuous prism
face identities and a proved finite signed-array identity. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f₀ f₁ : C(X, Y)}

def rawPrism (H : f₀.Homotopy f₁) (n : ℕ) :
    RawRationalChains X n →ₗ[ℚ] RawRationalChains Y (n + 1) :=
  Finsupp.linearCombination ℚ (fun simplex =>
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (homotopyPrism H i simplex) 1)

@[simp] theorem rawPrism_single_one (H : f₀.Homotopy f₁) (n : ℕ)
    (simplex : RawSingularSimplex X n) :
    rawPrism H n (Finsupp.single simplex 1) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (homotopyPrism H i simplex) 1 := by
  simp [rawPrism]

theorem rawPrism_boundary_single (H : f₀.Homotopy f₁) (n : ℕ)
    (simplex : RawSingularSimplex X (n + 1)) :
    rawBoundary (n + 1) (rawPrism H (n + 1) (Finsupp.single simplex 1)) +
      rawPrism H n (rawBoundary n (Finsupp.single simplex 1)) =
        Finsupp.single (f₁.comp simplex) 1 - Finsupp.single (f₀.comp simplex) 1 := by
  let u : Fin (n + 2) → Fin (n + 3) → RawRationalChains Y (n + 1) := fun i j =>
    (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) •
      Finsupp.single ((homotopyPrism H i simplex).comp (face j)) 1
  let v : Fin (n + 1) → Fin (n + 2) → RawRationalChains Y (n + 1) := fun i j =>
    (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) •
      Finsupp.single (homotopyPrism H i (simplex.comp (face j))) 1
  have hlower (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
      u i.succ j.castSucc = -v i j := by
    dsimp only [u, v]
    rw [homotopyPrism_face_before H i j h]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    rw [show (i : ℕ) + 1 + (j : ℕ) = ((i : ℕ) + (j : ℕ)) + 1 by omega,
      pow_succ, mul_neg_one, neg_smul]
  have hupper (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j) :
      u i.castSucc j.succ = -v i j := by
    dsimp only [u, v]
    rw [homotopyPrism_face_after H i j h]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    rw [show (i : ℕ) + ((j : ℕ) + 1) = ((i : ℕ) + (j : ℕ)) + 1 by omega,
      pow_succ, mul_neg_one, neg_smul]
  have hdiagonal (i : Fin (n + 1)) :
      u i.castSucc i.succ.castSucc = -u i.succ i.succ.castSucc := by
    dsimp only [u]
    rw [homotopyPrism_face_middle H i]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    rw [show ((i : ℕ) + 1) + ((i : ℕ) + 1) = ((i : ℕ) + ((i : ℕ) + 1)) + 1 by omega,
      pow_succ, mul_neg_one, neg_smul, neg_neg]
  have hc := signed_prism_cancellation n u v hlower hupper hdiagonal
  have hleft : rawBoundary (n + 1) (rawPrism H (n + 1) (Finsupp.single simplex 1)) =
      ∑ i, ∑ j, u i j := by
    simp only [rawPrism_single_one, map_sum, map_zsmul, rawBoundary_single,
      Finset.smul_sum, smul_smul, ← pow_add, u]
  have hright : rawPrism H n (rawBoundary n (Finsupp.single simplex 1)) =
      ∑ i, ∑ j, v i j := by
    simp only [rawBoundary_single, map_sum, map_zsmul, rawPrism_single_one,
      Finset.smul_sum, smul_smul, ← pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [v, Nat.add_comm]
  have hOdd : Odd ((n + 1) + (n + 2)) := ⟨n + 1, by omega⟩
  rw [hleft, hright, hc]
  simp only [u, Fin.val_zero, zero_add, pow_zero, one_smul, homotopyPrism_face_top,
    Fin.val_last, hOdd.neg_one_pow, homotopyPrism_face_bottom, neg_one_smul, sub_eq_add_neg]

theorem rawPrism_chain_identity (H : f₀.Homotopy f₁) (n : ℕ) :
    (rawBoundary (n + 1)).comp (rawPrism H (n + 1)) +
      (rawPrism H n).comp (rawBoundary n) =
        rawChainMap f₁ (n + 1) - rawChainMap f₀ (n + 1) := by
  apply Finsupp.lhom_ext
  intro simplex a
  have hsingle : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
      rawPrism_boundary_single H n simplex

end BanachIsometric.SingularPrism
