import JLMS.OrdinalLimitRows

/-!
# Selecting limit rows beyond a prescribed cutoff

The initial part of an operator's standard matrix can be excluded by shifting
the normal enumeration before selecting its limit indices. The resulting
single projection can be used simultaneously for a family of operators.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace
  ordinalLimitOperatorGroup ordinalLimitOperatorSpace ordinalLimitOperatorAlgebra
  ordinalLimitOperatorScalarTower ordinalLimitOperatorScalarComm

def initialOrdinalTailLimitIndices {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    {β : Ordinal.{u}} (hβ : β < c.ord) :
    C(OrdinalInterval c.ord, OrdinalInterval c.ord) :=
  (ordinalTailShift c.ord β (initialOrdinal_succ_add hc.le hβ)).comp
    (initialOrdinalLimitIndices hc)

theorem initialOrdinalTailLimitIndices_strictMono {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    {β : Ordinal.{u}} (hβ : β < c.ord) : StrictMono (initialOrdinalTailLimitIndices hc hβ) :=
  (ordinalTailShift_strictMono c.ord β (initialOrdinal_succ_add hc.le hβ)).comp
    (initialOrdinalLimitIndices_strictMono hc)

@[simp] theorem initialOrdinalTailLimitIndices_endpoint {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord) :
    initialOrdinalTailLimitIndices hc hβ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
  simp [initialOrdinalTailLimitIndices]

theorem initialOrdinalTailLimitIndices_above {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (x : OrdinalInterval c.ord) : β < (initialOrdinalTailLimitIndices hc hβ x).val :=
  ordinalTailShift_above c.ord β (initialOrdinal_succ_add hc.le hβ) _

theorem initialOrdinalTailLimitIndices_isSuccLimit {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (x : OrdinalInterval c.ord) :
    Order.IsSuccLimit (initialOrdinalTailLimitIndices hc hβ x).val :=
  (Ordinal.isNormal_add_right (Order.succ β)).map_isSuccLimit
    (initialOrdinalLimitIndices_isSuccLimit hc x)

def ordinalTailLimitRowsSelector {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c)
    {β : Ordinal.{u}} (hβ : β < c.ord)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) :
    C(OrdinalInterval c.ord, OrdinalInterval c.ord) :=
  φ.comp (initialOrdinalTailLimitIndices hc hβ)

theorem ordinalTailLimitRowsSelector_strictMono {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) (hφ : StrictMono φ) :
    StrictMono (ordinalTailLimitRowsSelector hc hβ φ) :=
  hφ.comp (initialOrdinalTailLimitIndices_strictMono hc hβ)

@[simp] theorem ordinalTailLimitRowsSelector_endpoint {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord))
    (hφ : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) :
    ordinalTailLimitRowsSelector hc hβ φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
  change φ (initialOrdinalTailLimitIndices hc hβ _) = _
  rw [initialOrdinalTailLimitIndices_endpoint, hφ]

theorem ordinalTailLimitRowsSelector_above {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) (hφ : StrictMono φ)
    (x : OrdinalInterval c.ord) : β < (ordinalTailLimitRowsSelector hc hβ φ x).val :=
  (initialOrdinalTailLimitIndices_above hc hβ x).trans_le (hφ.id_le _)

/-- One projection kills every operator whose sufficiently late limit rows vanish. -/
theorem ordinalTailLimitRowsProjection_comp_eq_zero {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) (hφ : StrictMono φ)
    (hφtop : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hzero : ∀ (f : OrdinalC 𝕜 c.ord) (x : OrdinalInterval c.ord),
      Order.IsSuccLimit x.val → β < (φ x).val → T f (φ x) = 0) :
    (ordinalCeilingProjection c.ord (ordinalTailLimitRowsSelector hc hβ φ)
      (ordinalTailLimitRowsSelector_strictMono hc hβ φ hφ).monotone
      (ordinalTailLimitRowsSelector_endpoint hc hβ φ hφtop)).comp T = 0 := by
  apply ordinalCeilingProjection_comp_eq_zero
  intro f x
  exact hzero f (initialOrdinalTailLimitIndices hc hβ x)
    (initialOrdinalTailLimitIndices_isSuccLimit hc hβ x)
    (ordinalTailLimitRowsSelector_above hc hβ φ hφ x)

theorem mem_continuityIdeal_of_zero_limit_rows_above
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : Cardinal.aleph0 < c) {β : Ordinal.{u}} (hβ : β < c.ord)
    (φ : C(OrdinalInterval c.ord, OrdinalInterval c.ord)) (hφ : StrictMono φ)
    (hφtop : φ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hzero : ∀ (f : OrdinalC 𝕜 c.ord) (x : OrdinalInterval c.ord),
      Order.IsSuccLimit x.val → β < (φ x).val → T f (φ x) = 0) :
    T ∈ continuityIdeal (𝕜 := 𝕜) (B := OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (A := A) θ := by
  apply mem_continuityIdeal_of_zero_cofinal_rows c.ord (ordinalTailLimitRowsSelector hc hβ φ)
    (ordinalTailLimitRowsSelector_strictMono hc hβ φ hφ)
    (ordinalTailLimitRowsSelector_endpoint hc hβ φ hφtop) θ T
  intro f x
  exact hzero f (initialOrdinalTailLimitIndices hc hβ x)
    (initialOrdinalTailLimitIndices_isSuccLimit hc hβ x)
    (ordinalTailLimitRowsSelector_above hc hβ φ hφ x)

end JLMS
