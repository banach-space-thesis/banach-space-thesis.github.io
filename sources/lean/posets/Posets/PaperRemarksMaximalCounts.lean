import Posets.IdealCountRealization
import PosetsCommon.MaximalIdeals

/-! Introduction, paragraph before Proposition 1.10: each positive finite
number of maximal ideals is realized. The positive-size convention is explicit.
Ordinary maximal ideals and maximal closed ideals are identified by the proved
Banach-algebra maximality theorem. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

theorem paper_positive_number_maximal_ideals (n : ℕ) :
    ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
      Nonempty (MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃ Fin (n + 1)) ∧
      Nonempty ({I : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) // IsMaximalAlgebraIdeal 𝕜 I} ≃
        Fin (n + 1)) := by
  obtain ⟨𝒜, h𝒜, _, hmax⟩ := exists_space_with_idealCounts (𝕜 := 𝕜)
    0 (fun _ : Fin 1 => Fin (n + 1)) (by norm_num)
  have hmax' : Nonempty (MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃
      Fin (n + 1)) := by simpa using hmax
  obtain ⟨e⟩ := hmax'
  let e₀ : {I : Set (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) // IsMaximalAlgebraIdeal 𝕜 I} ≃
      MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) :=
    { toFun := fun I => ⟨I.val, (isMaximalAlgebraIdeal_iff_isMaximalClosedIdeal I.val).mp I.property⟩
      invFun := fun I => ⟨I.val, (isMaximalAlgebraIdeal_iff_isMaximalClosedIdeal I.val).mpr I.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨𝒜, h𝒜, ⟨e⟩, ⟨e₀.trans e⟩⟩

end Posets
