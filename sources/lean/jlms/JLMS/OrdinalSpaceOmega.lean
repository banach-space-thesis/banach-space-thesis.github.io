import JLMS.OrdinalSpaceEndpointZero
import JLMS.CZeroSumEquiv
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The countable initial ordinal space

The interval [0,ω] is the one-point compactification of the natural
numbers. Restriction to the finite ordinals identifies its endpoint-zero
functions isometrically with c₀. This gives the countable base case in
the ordinal-space classification, including the square isomorphism.
-/

noncomputable section
open Filter Topology Set Ordinal
open scoped Ordinal
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalOmegaNatPoint (n : ℕ) : OrdinalInterval (ω : Ordinal.{u}) :=
  ⟨n, Ordinal.zero_le _, (Ordinal.nat_lt_omega0 n).le⟩

def ordinalOmegaEndpoint : OrdinalInterval (ω : Ordinal.{u}) :=
  ⟨ω, Ordinal.zero_le _, le_rfl⟩

theorem tendsto_ordinalOmegaNatPoint :
    Tendsto ordinalOmegaNatPoint.{u} atTop (𝓝 ordinalOmegaEndpoint) := by
  apply tendsto_subtype_rng.2
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.1 ha
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    change (k : Ordinal) < (n : Ordinal)
    exact_mod_cast (Nat.lt_of_succ_le hn)
  · intro a ha
    exact Eventually.of_forall fun n => (Ordinal.nat_lt_omega0 n).trans ha

def ordinalOmegaOnePointMap : OnePoint ℕ → OrdinalInterval (ω : Ordinal.{u}) :=
  OnePoint.rec ordinalOmegaEndpoint ordinalOmegaNatPoint

theorem continuous_ordinalOmegaOnePointMap : Continuous ordinalOmegaOnePointMap.{u} :=
  (OnePoint.continuous_iff_from_nat _).2 tendsto_ordinalOmegaNatPoint

theorem ordinalOmegaOnePointMap_bijective : Function.Bijective ordinalOmegaOnePointMap.{u} := by
  constructor
  · intro x y h
    induction x using OnePoint.rec with
    | infty =>
      induction y using OnePoint.rec with
      | infty => rfl
      | coe n =>
        have hval : (ω : Ordinal.{u}) = n := congrArg Subtype.val h
        exact ((Ordinal.nat_lt_omega0 n).ne hval.symm).elim
    | coe n =>
      induction y using OnePoint.rec with
      | infty =>
        have hval : (n : Ordinal.{u}) = ω := congrArg Subtype.val h
        exact ((Ordinal.nat_lt_omega0 n).ne hval).elim
      | coe m =>
        congr 1
        have hval : (n : Ordinal.{u}) = m := congrArg Subtype.val h
        exact_mod_cast hval
  · intro a
    obtain ha | ha := lt_or_eq_of_le a.property.2
    · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 ha
      exact ⟨(n : OnePoint ℕ), Subtype.ext hn.symm⟩
    · exact ⟨OnePoint.infty, Subtype.ext ha.symm⟩

/-- The canonical one-point compactification model of [0,ω]. -/
def ordinalOmegaOnePointHomeomorph : OnePoint ℕ ≃ₜ OrdinalInterval (ω : Ordinal.{u}) :=
  (Equiv.ofBijective _ ordinalOmegaOnePointMap_bijective).toHomeomorphOfContinuousClosed
    continuous_ordinalOmegaOnePointMap continuous_ordinalOmegaOnePointMap.isClosedMap

@[simp] theorem ordinalOmegaOnePointHomeomorph_coe (n : ℕ) :
    ordinalOmegaOnePointHomeomorph.{u} (n : OnePoint ℕ) = ordinalOmegaNatPoint n := rfl

@[simp] theorem ordinalOmegaOnePointHomeomorph_infty :
    ordinalOmegaOnePointHomeomorph.{u} OnePoint.infty = ordinalOmegaEndpoint := rfl

local instance ordinalOmegaEndpointGroup :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 (ω : Ordinal.{u})) := inferInstance
local instance ordinalOmegaEndpointSpace :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 (ω : Ordinal.{u})) := inferInstance
local instance ordinalOmegaSumGroup : NormedAddCommGroup (CZeroSum 𝕜 (fun _ : ℕ => 𝕜)) :=
  inferInstance
local instance ordinalOmegaSumSpace : NormedSpace 𝕜 (CZeroSum 𝕜 (fun _ : ℕ => 𝕜)) :=
  inferInstance

theorem ordinalOmegaEndpoint_tendsto (f : ordinalEndpointZero 𝕜 (ω : Ordinal.{u})) :
    Tendsto (fun n => f.val (ordinalOmegaNatPoint n)) cofinite (𝓝 0) := by
  have hf : f.val ordinalOmegaEndpoint = 0 := f.property
  rw [Nat.cofinite_eq_atTop]
  simpa only [hf] using f.val.continuous.tendsto ordinalOmegaEndpoint |>.comp
    tendsto_ordinalOmegaNatPoint

def ordinalOmegaEndpointRestriction (f : ordinalEndpointZero 𝕜 (ω : Ordinal.{u})) :
    CZeroSum 𝕜 (fun _ : ℕ => 𝕜) :=
  CZeroSum.mk (fun n => f.val (ordinalOmegaNatPoint n))
    (by simpa only [norm_zero] using (ordinalOmegaEndpoint_tendsto f).norm)

@[simp] theorem ordinalOmegaEndpointRestriction_apply
    (f : ordinalEndpointZero 𝕜 (ω : Ordinal.{u})) (n : ℕ) :
    ordinalOmegaEndpointRestriction f n = f.val (ordinalOmegaNatPoint n) := rfl

theorem norm_ordinalOmegaEndpointRestriction (f : ordinalEndpointZero 𝕜 (ω : Ordinal.{u})) :
    ‖ordinalOmegaEndpointRestriction f‖ = ‖f‖ := by
  apply le_antisymm
  · apply CZeroSum.norm_le (norm_nonneg f)
    intro n
    exact f.val.norm_coe_le_norm (ordinalOmegaNatPoint n)
  · change ‖f.val‖ ≤ ‖ordinalOmegaEndpointRestriction f‖
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro a
    obtain ha | ha := lt_or_eq_of_le a.property.2
    · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 ha
      have hpoint : a = ordinalOmegaNatPoint n := Subtype.ext hn
      rw [hpoint]
      exact (ordinalOmegaEndpointRestriction f).norm_apply_le_norm n
    · have hpoint : a = ordinalOmegaEndpoint := Subtype.ext ha
      have hf : f.val ordinalOmegaEndpoint = 0 := f.property
      rw [hpoint, hf, norm_zero]
      exact norm_nonneg _

theorem ordinalOmegaEndpointRestriction_surjective :
    Function.Surjective (ordinalOmegaEndpointRestriction.{u} (𝕜 := 𝕜)) := by
  intro x
  let g : C(OnePoint ℕ, 𝕜) := OnePoint.continuousMapMkDiscrete x 0
    ((tendsto_zero_iff_norm_tendsto_zero).2 x.tendsto_norm)
  let e := ordinalOmegaOnePointHomeomorph.{u}
  let f : OrdinalC 𝕜 (ω : Ordinal.{u}) := ⟨fun a => g (e.symm a),
    g.continuous.comp e.symm.continuous⟩
  have hf : f ∈ ordinalEndpointZero 𝕜 (ω : Ordinal.{u}) := by
    change g (e.symm (e OnePoint.infty)) = 0
    rw [e.symm_apply_apply]
    rfl
  refine ⟨⟨f, hf⟩, ?_⟩
  ext n
  change g (e.symm (e (n : OnePoint ℕ))) = x n
  rw [e.symm_apply_apply]
  rfl

/-- Endpoint-zero functions on [0,ω] are exactly the usual null sequences. -/
def ordinalOmegaEndpointCZeroIsometry :
    ordinalEndpointZero 𝕜 (ω : Ordinal.{u}) ≃ₗᵢ[𝕜] CZeroSum 𝕜 (fun _ : ℕ => 𝕜) :=
  LinearIsometryEquiv.ofSurjective
    { toFun := ordinalOmegaEndpointRestriction
      map_add' f g := by ext n; rfl
      map_smul' c f := by ext n; rfl
      norm_map' := norm_ordinalOmegaEndpointRestriction }
    ordinalOmegaEndpointRestriction_surjective

/-- The countable initial ordinal function space is isomorphic to c₀. -/
def ordinalSpaceOmegaCZeroEquiv :
    OrdinalC 𝕜 (ω : Ordinal.{u}) ≃L[𝕜] CZeroSum 𝕜 (fun _ : ℕ => 𝕜) :=
  (ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) ω le_rfl).trans
    ordinalOmegaEndpointCZeroIsometry.toContinuousLinearEquiv

/-- The countable base case of the square-isomorphism classification. -/
def ordinalSpaceOmegaSquareEquiv :
    OrdinalC 𝕜 (ω : Ordinal.{u}) ≃L[𝕜]
      OrdinalC 𝕜 (ω : Ordinal.{u}) × OrdinalC 𝕜 (ω : Ordinal.{u}) :=
  ordinalSpaceOmegaCZeroEquiv.trans
    ((CZeroSum.infiniteSquareIsometry (𝕜 := 𝕜) ℕ 𝕜).toContinuousLinearEquiv.trans
      (ordinalSpaceOmegaCZeroEquiv.symm.prodCongr ordinalSpaceOmegaCZeroEquiv.symm))

end JLMS
