import Posets.Models
import PosetsCommon.NoncommutativeQuotient
import PosetsCommon.SeparableOperatorIdeal

noncomputable section
namespace Posets
variable (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The same separable-range subspace, regarded as a left ideal in the
operator algebra. Its carrier is unchanged. -/
def separableRangeLeftIdeal : Ideal (E →L[𝕜] E) where
  carrier := {T | JFA.HasSeparableRange 𝕜 E E T}
  zero_mem' := JFA.hasSeparableRange_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun S _ hT => hT.comp_left S

instance separableRangeLeftIdeal_twoSided : (separableRangeLeftIdeal 𝕜 E).IsTwoSided :=
  ⟨fun {_} S hT => hT.comp_right S⟩

instance separableRangeLeftIdeal_closed :
    IsClosed (separableRangeLeftIdeal 𝕜 E : Set (E →L[𝕜] E)) :=
  JFA.isClosed_separableOperators

/-- The ring quotient and the paper's existing normed vector quotient have
the same additive equivalence relation, hence the same underlying type. -/
instance separableQuotientRing : Ring (SeparableQuotient 𝕜 E) :=
  Ideal.Quotient.ring (separableRangeLeftIdeal 𝕜 E)

instance separableQuotientNormedRing : NormedRing (SeparableQuotient 𝕜 E) :=
  ThesisCommon.noncommutativeQuotientNormedRing (separableRangeLeftIdeal 𝕜 E)

instance separableQuotientAlgebra : Algebra 𝕜 (SeparableQuotient 𝕜 E) :=
  Ideal.Quotient.algebra 𝕜 (A := E →L[𝕜] E) (I := separableRangeLeftIdeal 𝕜 E)

instance separableQuotientNormedAlgebra : NormedAlgebra 𝕜 (SeparableQuotient 𝕜 E) :=
  ThesisCommon.noncommutativeQuotientNormedAlgebra (separableRangeLeftIdeal 𝕜 E) 𝕜

/-- The norm has not been transported or replaced: it is definitionally the
original vector quotient norm from `Models`. -/
theorem separableQuotient_norm_eq_original (x : SeparableQuotient 𝕜 E) :
    ‖x‖ = @norm (SeparableQuotient 𝕜 E)
      (Submodule.Quotient.seminormedAddCommGroup
        (JFA.separableRangeSubmodule (𝕜 := 𝕜) (E := E) (F := E))).toNorm x := rfl

theorem separableQuotient_completeSpace [CompleteSpace E] :
    CompleteSpace (SeparableQuotient 𝕜 E) := inferInstance

@[simp] theorem quotientMap_mul (S T : E →L[𝕜] E) :
    quotientMap 𝕜 E (S * T) = quotientMap 𝕜 E S * quotientMap 𝕜 E T := rfl

@[simp] theorem quotientMap_one :
    quotientMap 𝕜 E 1 = (1 : SeparableQuotient 𝕜 E) := rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap 𝕜 E) :=
  Submodule.mkQ_surjective _

@[simp] theorem quotientMap_eq_zero_iff (T : E →L[𝕜] E) :
    quotientMap 𝕜 E T = 0 ↔ JFA.HasSeparableRange 𝕜 E E T :=
  Submodule.Quotient.mk_eq_zero _

/-- The paper's quotient map as an actual algebra homomorphism. -/
def quotientMapAlgHom : (E →L[𝕜] E) →ₐ[𝕜] SeparableQuotient 𝕜 E :=
  Ideal.Quotient.mkₐ 𝕜 (separableRangeLeftIdeal 𝕜 E)

@[simp] theorem quotientMapAlgHom_apply (T : E →L[𝕜] E) :
    quotientMapAlgHom 𝕜 E T = quotientMap 𝕜 E T := rfl

theorem quotientMap_norm_le (T : E →L[𝕜] E) : ‖quotientMap 𝕜 E T‖ ≤ ‖T‖ :=
  Submodule.Quotient.norm_mk_le _ T

/-- The canonical quotient homomorphism is contractive. -/
def quotientMapBoundedHom : ThesisCommon.BoundedHom 𝕜 (E →L[𝕜] E) (SeparableQuotient 𝕜 E) where
  toContinuousLinearMap := (quotientMap 𝕜 E).mkContinuous 1
    (fun T => by simpa only [one_mul] using quotientMap_norm_le 𝕜 E T)
  map_mul' := quotientMap_mul 𝕜 E

@[simp] theorem quotientMapBoundedHom_apply (T : E →L[𝕜] E) :
    quotientMapBoundedHom 𝕜 E T = quotientMap 𝕜 E T := rfl

/-- Quantifying multiplication over arbitrary representatives is exactly the
ordinary closed two-sided ideal condition in the bundled quotient algebra. -/
theorem isQuotientClosedIdeal_iff (I : Set (SeparableQuotient 𝕜 E)) :
    IsQuotientClosedIdeal 𝕜 E I ↔ ThesisCommon.IsClosedIdeal 𝕜 I := by
  constructor
  · rintro ⟨hc, h0, ha, hs, hm⟩
    refine ⟨hc, h0, ha, hs, ?_⟩
    intro a b hb
    obtain ⟨A, rfl⟩ := quotientMap_surjective 𝕜 E a
    obtain ⟨B, rfl⟩ := quotientMap_surjective 𝕜 E b
    simpa only [quotientMap_mul] using hm A B hb
  · rintro ⟨hc, h0, ha, hs, hm⟩
    refine ⟨hc, h0, ha, hs, ?_⟩
    intro A B hB
    simpa only [quotientMap_mul] using hm (quotientMap 𝕜 E A) (quotientMap 𝕜 E B) hB

/-- Identity on carriers identifies the statement layer's quotient ideals
with the ordinary closed ideals of the actual normed quotient algebra. -/
def quotientClosedIdealOrderIso :
    QuotientClosedIdeals 𝕜 E ≃o ThesisCommon.ClosedIdeal 𝕜 (SeparableQuotient 𝕜 E) where
  toFun I := ⟨I.val, (isQuotientClosedIdeal_iff 𝕜 E I.val).mp I.property⟩
  invFun I := ⟨I.val, (isQuotientClosedIdeal_iff 𝕜 E I.val).mpr I.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

end Posets
