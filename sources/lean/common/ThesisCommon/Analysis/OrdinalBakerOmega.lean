import ThesisCommon.Analysis.OrdinalBakerOrder
import Mathlib.Data.Set.Finite.Lattice

/-! The first infinite stage of the closed-copy classification. Every
infinite compact ordinal set contains a closed copy of [0,ω], and a finite
closed cover of [0,ω] has a member containing such a copy. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinal_finite_Iic_nat (n : ℕ) : (Iic (n : Ordinal.{u})).Finite := by
  induction n with
  | zero =>
      change (Iic (⊥ : Ordinal.{u})).Finite
      rw [Iic_bot]
      exact finite_singleton _
  | succ n ih =>
      rw [Ordinal.natCast_succ, Iic_succ]
      exact ih.insert _

theorem ordinal_finite_Iic_of_lt_omega {β : Ordinal.{u}} (hβ : β < Ordinal.omega0) :
    (Iic β).Finite := by
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hβ
  exact ordinal_finite_Iic_nat n

theorem ordinal_infinite_compact_contains_omega {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hinf : A.Infinite) :
    ∃ f : C(OrdinalInterval Ordinal.omega0.{u}, Ordinal.{u}),
      Function.Injective f ∧ range f ⊆ A := by
  obtain ⟨β, e, he, _⟩ := ordinal_compact_order_homeomorph hA hinf.nonempty
  have hβ : Ordinal.omega0 ≤ β := by
    by_contra! h
    have hfin : (Icc (0 : Ordinal.{u}) β).Finite :=
      (ordinal_finite_Iic_of_lt_omega h).subset Icc_subset_Iic_self
    letI : Finite (OrdinalInterval β) := hfin.to_subtype
    letI : Finite A := Finite.of_equiv (OrdinalInterval β) e.toEquiv
    exact hinf (finite_coe_iff.mp inferInstance)
  let g : C(OrdinalInterval Ordinal.omega0.{u}, OrdinalInterval β) :=
    ⟨fun x => ⟨x.val, x.property.1, x.property.2.trans hβ⟩,
      continuous_subtype_val.subtype_mk _⟩
  let f : C(OrdinalInterval Ordinal.omega0.{u}, Ordinal.{u}) :=
    ⟨fun x => (e (g x)).val,
      continuous_subtype_val.comp (e.continuous.comp g.continuous)⟩
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have hgxy : g x = g y := e.injective (Subtype.ext hxy)
    exact Subtype.ext (congrArg (fun z : OrdinalInterval β => z.val) hgxy)
  · rintro _ ⟨x, rfl⟩
    exact (e (g x)).property

theorem ordinal_Iic_omega_infinite : (Iic (Ordinal.omega0 : Ordinal.{u})).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => (n : Ordinal.{u})) := Nat.cast_injective
  apply (infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact (Ordinal.nat_lt_omega0 n).le

/-- The genuine rank-one finite closed-cover theorem, with its actual
continuous closed copy represented as `OrdinalClosedCopy`. -/
theorem ordinal_omega_finite_closed_cover {ι : Type*} [Finite ι]
    (A : ι → Set Ordinal.{u}) (hA : ∀ i, IsClosed (A i))
    (hcover : Iic (Ordinal.omega0 : Ordinal.{u}) = ⋃ i, A i) :
    ∃ i, ∃ f : OrdinalClosedCopy Ordinal.omega0.{u} Ordinal.omega0.{u},
      ∀ x, (f.val x).val ∈ A i := by
  classical
  have hi : ∃ i, (A i).Infinite := by
    by_contra! h
    have hu : (⋃ i, A i).Finite := finite_iUnion (fun i => not_not.mp (h i))
    rw [← hcover] at hu
    exact ordinal_Iic_omega_infinite hu
  obtain ⟨i, hi⟩ := hi
  have hsub : A i ⊆ Iic (Ordinal.omega0 : Ordinal.{u}) := by
    rw [hcover]
    exact subset_iUnion A i
  have hcompact : IsCompact (A i) := by
    apply (isCompact_Icc : IsCompact (Icc (0 : Ordinal.{u}) Ordinal.omega0)).of_isClosed_subset (hA i)
    intro x hx
    exact ⟨bot_le, hsub hx⟩
  obtain ⟨f, hfinj, hfA⟩ := ordinal_infinite_compact_contains_omega hcompact hi
  let g : C(OrdinalInterval Ordinal.omega0.{u}, OrdinalInterval Ordinal.omega0.{u}) :=
    ⟨fun x => ⟨f x, bot_le, hsub (hfA (mem_range_self x))⟩, f.continuous.subtype_mk _⟩
  refine ⟨i, ⟨g, ?_⟩, ?_⟩
  · intro x y hxy
    exact hfinj (congrArg Subtype.val hxy)
  · intro x
    exact hfA (mem_range_self x)

end ThesisCommon
