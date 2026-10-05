import Posets.OrdinalVariableUnitParameters
import Posets.OrdinalVaryingRankUnits

/-! Concrete cofinal ordinal arithmetic supplies the varying-unit parameters
at every additive-principal limit rank of countable cofinality. -/

noncomputable section
universe u
namespace Posets

theorem exists_ordinalVariableUnitParameters
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hcf : γ.cof = Cardinal.aleph0) (N : ℕ) :
    Nonempty (OrdinalVariableUnitParameters γ N) := by
  obtain ⟨R⟩ := exists_ordinalVaryingRankUnits γ hP hω hcf (fun _ => (N+1)*2)
  exact ⟨{
    unit := R.unit
    unit_large := R.infinite
    sourceStrictMono := R.source_strictMono (fun _ => by omega)
    source_lt := R.source_below
    cofinal := R.cofinal }⟩

end Posets
