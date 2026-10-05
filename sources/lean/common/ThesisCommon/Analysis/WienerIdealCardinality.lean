import ThesisCommon.Analysis.WienerMaximalIdeals
import ThesisCommon.Analysis.BanachTwoSidedIdeals
import ThesisCommon.Analysis.ClosedSetsCardinality
import ThesisCommon.Analysis.CountableSumSeparable

/-! Exact continuum cardinality, conditional on the two genuine structural
assertions in the source: the strictly-singular Wiener quotient and containment
of the strictly singular operators in every maximal ideal. The lower bound
does not need the containment assertion; the upper bound uses closedness and
second countability of the actual quotient, not a classification assumed as data.
-/
noncomputable section
open Topology TopologicalSpace
namespace ThesisCommon
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem operatorIdeal_preimage_image_of_ker_le
    (q : (X →L[ℂ] X) →ₗ[ℂ] Y) (J : TwoSidedIdeal (X →L[ℂ] X))
    (hker : LinearMap.ker q ≤ operatorIdealSubmodule J) :
    q ⁻¹' (q '' (J : Set (X →L[ℂ] X))) = (J : Set (X →L[ℂ] X)) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hdiff : x - y ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    simpa using J.add_mem (hker hdiff) hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable [CompleteSpace X]

theorem maximalIdeals_le_continuum_of_secondCountable_quotient
    [SecondCountableTopology Y] (q : (X →L[ℂ] X) →ₗ[ℂ] Y)
    (hq : IsQuotientMap q)
    (hker : ∀ J : TwoSidedIdeal (X →L[ℂ] X), IsCoatom J →
      LinearMap.ker q ≤ operatorIdealSubmodule J) :
    Cardinal.mk {J : TwoSidedIdeal (X →L[ℂ] X) // IsCoatom J} ≤ Cardinal.continuum := by
  let f : {J : TwoSidedIdeal (X →L[ℂ] X) // IsCoatom J} → Closeds Y := fun J =>
    ⟨q '' (J.val : Set (X →L[ℂ] X)), hq.isClosed_preimage.mp (by
      rw [operatorIdeal_preimage_image_of_ker_le q J.val (hker J.val J.property)]
      exact isClosed_of_isCoatom_twoSidedIdeal J.val J.property)⟩
  have hf : Function.Injective f := by
    intro J K h
    have heq : q '' (J.val : Set (X →L[ℂ] X)) = q '' (K.val : Set (X →L[ℂ] X)) :=
      congrArg (fun s : Closeds Y => (s : Set Y)) h
    have hp := congrArg (fun s : Set Y => q ⁻¹' s) heq
    dsimp only at hp
    rw [operatorIdeal_preimage_image_of_ker_le q J.val (hker J.val J.property),
      operatorIdeal_preimage_image_of_ker_le q K.val (hker K.val K.property)] at hp
    exact Subtype.ext (SetLike.coe_injective hp)
  have hle := Cardinal.lift_mk_le_lift_mk_of_injective hf
  have hup := Cardinal.lift_le.mpr (cardinal_closeds_le_continuum Y)
  have hbound := hle.trans hup
  simpa using hbound

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem HasStrictlySingularWienerQuotient.hasContinuumManyMaximalOperatorIdeals
    (h : HasStrictlySingularWienerQuotient ℂ X)
    (hall : AllMaximalIdealsContainStrictlySingular ℂ X) :
    HasContinuumManyMaximalOperatorIdeals ℂ X := by
  apply le_antisymm _ h.continuum_le_maximalIdeals
  obtain ⟨J, hJ, hclosed, e, heunit, hemul⟩ := h
  letI : IsClosed (operatorIdealSubmodule J : Set (X →L[ℂ] X)) := hclosed
  letI : SeparableSpace (WienerSequences ℂ) :=
    lp_separableSpace_of_countable (𝕜 := ℂ) 1 (by simp)
  let q : (X →L[ℂ] X) →ₗ[ℂ] WienerSequences ℂ :=
    e.toLinearMap.comp (operatorIdealSubmodule J).mkQ
  have hquot : IsQuotientMap q :=
    e.toHomeomorph.isQuotientMap.comp (operatorIdealSubmodule J).isOpenQuotientMap_mkQ.isQuotientMap
  apply maximalIdeals_le_continuum_of_secondCountable_quotient q hquot
  intro K hK T hT
  have hz : e ((operatorIdealSubmodule J).mkQ T) = 0 := hT
  have hz' : (operatorIdealSubmodule J).mkQ T = 0 := e.injective (hz.trans e.map_zero.symm)
  have hmem : T ∈ operatorIdealSubmodule J := by
    have hk : T ∈ LinearMap.ker (operatorIdealSubmodule J).mkQ := hz'
    simpa only [Submodule.ker_mkQ] using hk
  exact hall K hK T ((hJ T).mp hmem)

end ThesisCommon
