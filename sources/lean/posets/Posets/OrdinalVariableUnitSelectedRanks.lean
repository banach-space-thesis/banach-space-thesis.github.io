import Posets.OrdinalVariableUnitColouredCores

/-! The concrete target ranks stay strictly increasing and cofinal after
the coloured core selection. -/

noncomputable section
open Set
universe u
namespace Posets

variable {𝕜 : Type*} [RCLike 𝕜] {γ : Ordinal.{u}} {N : ℕ}
  {P : OrdinalVariableUnitParameters γ N}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ))}
  {T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))} {ε δ : ℝ}

namespace OrdinalVariableUnitColouredCores

variable (F : OrdinalVariableUnitColouredCores P M T S ε δ)

theorem selectedRank_strictMono : StrictMono (fun i => P.sourceUnit (F.index i)) :=
  P.sourceUnit_strictMono.comp F.strictMono

theorem selectedRank_cofinal : ∀ β < γ, ∃ i, β < P.sourceUnit (F.index i) := by
  intro β hβ
  obtain ⟨n, hn⟩ := P.cofinal β hβ
  refine ⟨n, hn.trans_le (P.unit_strictMono.monotone ?_)⟩
  have hi := F.strictMono.id_le n
  change n ≤ F.index n at hi
  exact hi.trans (Nat.le_succ (F.index n))

theorem selectedRank_large (i : ℕ) : Ordinal.omega0 ≤ P.sourceUnit (F.index i) :=
  P.unit_large (F.index i+1)

theorem selectedRank_lt (i : ℕ) : P.sourceUnit (F.index i) < γ :=
  (P.unit (F.index i+1)).property

end OrdinalVariableUnitColouredCores
end Posets
