import JLMS.SignTreeLevels
import JLMS.CZeroCoordinateExtensions

/-!
# Coherent infinite sign tree and the resulting ℓ¹ embedding

Iterate the finite-level splitting, keeping the old vectors unchanged. For
any finite sign assignment, one branch realizes it on that level. Its dual
functional restricted to the finite span has norm at most two; Hahn–Banach
extends it to the entire space. The finite sign-tree estimate then produces
an actual bounded-below ℓ¹ synthesis operator.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_unit_finiteSignTree_of_stable_radius_one
    (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (hstable : ∀ b : NormalizedBlockSystem 𝕜, dualAsymptoticRadius (b.applyDual f) = 1) :
    ∃ v : ℕ → X, (∀ n, ‖v n‖ = 1) ∧ FiniteSignTree (𝕜 := 𝕜) v := by
  classical
  have hex (n : ℕ) (H : SignTreeLevel f n) := H.exists_next f hC hf hstable
  choose next hnext using hex
  let H : ∀ n, SignTreeLevel f n := Nat.rec (SignTreeLevel.zero f) (fun n level => next n level)
  let v (n : ℕ) := (H (n + 1)).vector (Fin.last n)
  have hcoherent (n : ℕ) (j : Fin n) : (H n).vector j = v j.val := by
    induction n with
    | zero => exact Fin.elim0 j
    | succ n ih =>
      refine Fin.lastCases rfl (fun i => ?_) j
      change (next n (H n)).vector i.castSucc = v i.val
      rw [hnext, ih]
  refine ⟨v, fun n => (H (n + 1)).unit _, ?_⟩
  intro F σ
  let m := F.sup id + 1
  let a : Fin m → Bool := fun j => σ j.val
  let D := finiteVectorSpan (𝕜 := 𝕜) (H m).vector
  let ψ := (f ((H m).branch a 0)).comp D.subtypeL
  obtain ⟨φ, hφ, hnorm⟩ := exists_extension_norm_eq D ψ
  refine ⟨φ, hnorm ▸ (H m).restriction a 0, ?_⟩
  intro n hn
  have hnm : n < m := lt_of_le_of_lt (Finset.le_sup (f := id) hn) (Nat.lt_succ_self _)
  let j : Fin m := ⟨n, hnm⟩
  have hmem : (H m).vector j ∈ D := mem_finiteVectorSpan _ j
  have he := hφ ⟨(H m).vector j, hmem⟩
  change φ ((H m).vector j) = f ((H m).branch a 0) ((H m).vector j) at he
  have hsign := (H m).sign a 0 j
  rw [← he, hcoherent] at hsign
  exact hsign

theorem containsEllOne_of_stable_radius_one [CompleteSpace X]
    (f : ℕ → (X →L[𝕜] 𝕜)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (hstable : ∀ b : NormalizedBlockSystem 𝕜, dualAsymptoticRadius (b.applyDual f) = 1) :
    ContainsEllOne 𝕜 X := by
  obtain ⟨v, hv, ht⟩ := exists_unit_finiteSignTree_of_stable_radius_one f hC hf hstable
  exact containsEllOne_of_finiteSignTree v (fun n => (hv n).le) ht

end JLMS
