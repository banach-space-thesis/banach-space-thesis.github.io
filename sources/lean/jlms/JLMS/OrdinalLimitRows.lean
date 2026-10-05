import JLMS.OrdinalLimitProjection

/-!
# Selecting the limit rows of an ordinal block decomposition

For an uncountable initial ordinal κ, the map x ↦ ω(1+x) is normal,
takes only nonzero limit values, and fixes κ. Composing it with the normal
cut enumeration supplies the cofinal row selector used for Ogden's V.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace
  ordinalLimitOperatorGroup ordinalLimitOperatorSpace ordinalLimitOperatorAlgebra
  ordinalLimitOperatorScalarTower ordinalLimitOperatorScalarComm

theorem initialOrdinal_omega0_mul {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c) :
    Ordinal.omega0 * c.ord = c.ord := by
  apply Ordinal.principal_mul_iff_mul_left_eq.mp (Ordinal.principal_mul_ord hc.le)
  · exact Ordinal.omega0_pos
  · simpa only [← Cardinal.ord_aleph0, Cardinal.ord_lt_ord] using hc

def initialOrdinalLimitIndices {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c) :
    C(OrdinalInterval c.ord, OrdinalInterval c.ord) where
  toFun x := ⟨Ordinal.omega0 * (1 + x.val), Ordinal.zero_le _, by
    have hω : Ordinal.omega0 ≤ c.ord := by
      simpa only [← Cardinal.ord_aleph0, Cardinal.ord_le_ord] using hc.le
    calc
      Ordinal.omega0 * (1 + x.val) ≤ Ordinal.omega0 * (1 + c.ord) :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone
          (add_le_add_left x.property.2 1)
      _ = c.ord := by rw [Ordinal.one_add_of_omega0_le hω, initialOrdinal_omega0_mul hc]⟩
  continuous_toFun :=
    (((Ordinal.isNormal_mul_right Ordinal.omega0_pos).continuous.comp
      (Ordinal.isNormal_add_right 1).continuous).comp continuous_subtype_val).subtype_mk _

theorem initialOrdinalLimitIndices_strictMono {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c) :
    StrictMono (initialOrdinalLimitIndices hc) := by
  intro x y hxy
  exact (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono
    ((Ordinal.isNormal_add_right 1).strictMono hxy)

@[simp] theorem initialOrdinalLimitIndices_endpoint {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) :
    initialOrdinalLimitIndices hc ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
  apply Subtype.ext
  have hω : Ordinal.omega0 ≤ c.ord := by
    simpa only [← Cardinal.ord_aleph0, Cardinal.ord_le_ord] using hc.le
  change Ordinal.omega0 * (1 + c.ord) = c.ord
  rw [Ordinal.one_add_of_omega0_le hω, initialOrdinal_omega0_mul hc]

theorem initialOrdinalLimitIndices_isSuccLimit {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    (x : OrdinalInterval c.ord) : Order.IsSuccLimit (initialOrdinalLimitIndices hc x).val := by
  exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
    ((show (0 : Ordinal.{u}) < 1 by simp).trans_le (Ordinal.le_add_right _ _))

def ordinalLimitRowsSelector {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) :
    C(OrdinalInterval c.ord, OrdinalInterval c.ord) := φ.comp (initialOrdinalLimitIndices hc)

theorem ordinalLimitRowsSelector_strictMono {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) (hφ : StrictMono φ) :
    StrictMono (ordinalLimitRowsSelector hc φ) :=
  hφ.comp (initialOrdinalLimitIndices_strictMono hc)

@[simp] theorem ordinalLimitRowsSelector_endpoint {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hφ : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) :
    ordinalLimitRowsSelector hc φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
  change φ (initialOrdinalLimitIndices hc _) = _
  rw [initialOrdinalLimitIndices_endpoint, hφ]

/-- The final zero-row step of Ogden Proposition 6.16. -/
theorem mem_continuityIdeal_of_zero_limit_rows
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) (hφ : StrictMono φ)
    (hφtop : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hzero : ∀ (f : OrdinalC 𝕜 c.ord) (x : OrdinalInterval c.ord),
      Order.IsSuccLimit x.val → T f (φ x) = 0) :
    T ∈ continuityIdeal (𝕜 := 𝕜) (B := OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (A := A) θ := by
  apply mem_continuityIdeal_of_zero_cofinal_rows c.ord (ordinalLimitRowsSelector hc φ)
    (ordinalLimitRowsSelector_strictMono hc φ hφ)
    (ordinalLimitRowsSelector_endpoint hc φ hφtop) θ T
  intro f x
  exact hzero f (initialOrdinalLimitIndices hc x) (initialOrdinalLimitIndices_isSuccLimit hc x)

end JLMS
