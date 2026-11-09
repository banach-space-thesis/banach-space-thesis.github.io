import BanachIsometric.LocalToGlobal
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.WellFounded

/-!
# Cofinal quotient dimensions for a separating increasing grading

Theorem C uses that an antitone sequence of kernels with zero intersection
eventually has quotient dimension greater than any fixed available finite
dimension. The ambient space is not assumed finite-dimensional.

Alternative proof route: restrict the kernels to one finite-dimensional test
subspace. Their natural dimensions attain a minimum, so the restrictions
stabilize; separation makes the stable restriction zero. The quotient maps
are therefore eventually injective on that test subspace. This avoids
assuming the ambient quotient dimensions are finite.
-/

namespace BanachIsometric

open Module Submodule

variable {K X : Type*} [DivisionRing K] [AddCommGroup X] [Module K X]

/-- Nested subspaces with equal finite codimension agree. Surjectivity of the
canonical quotient factor becomes injectivity by equality of finite dimensions.
The ambient space itself need not be finite-dimensional. -/
theorem submodule_eq_of_le_of_quotient_finrank_eq
    {U V : Submodule K X} (hUV : U ≤ V) [FiniteDimensional K (X ⧸ U)]
    (hdim : finrank K (X ⧸ U) = finrank K (X ⧸ V)) : U = V := by
  let f : (X ⧸ U) →ₗ[K] X ⧸ V := Submodule.factor hUV
  have hsurj : Function.Surjective f := Submodule.factor_surjective hUV
  letI : FiniteDimensional K (X ⧸ V) := Module.Finite.of_surjective f hsurj
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  apply le_antisymm hUV
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero U).mp
  apply hinj
  simpa only [f, Submodule.factor_mk, map_zero, Submodule.mkQ_apply] using
    ((Submodule.Quotient.mk_eq_zero V).mpr hx : (Submodule.Quotient.mk x : X ⧸ V) = 0)

/-- An antitone sequence of subspaces in a finite-dimensional space eventually
equals its full intersection. The indices are not assumed to become equal at
the first repeated dimension; a global minimum dimension is used instead. -/
theorem antitone_submodules_eventually_eq_iInf [FiniteDimensional K X]
    (N : ℕ → Submodule K X) (hN : Antitone N) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, N k = ⨅ j, N j := by
  classical
  obtain ⟨d, hd, hmin⟩ := wellFounded_lt.has_min
    (Set.range (fun k : ℕ => finrank K (N k))) ⟨_, 0, rfl⟩
  obtain ⟨k₀, rfl⟩ := hd
  have hstable (k : ℕ) (hk : k₀ ≤ k) : N k = N k₀ := by
    apply Submodule.eq_of_le_of_finrank_le (hN hk)
    exact le_of_not_gt (hmin _ ⟨k, rfl⟩)
  have hzero : N k₀ = ⨅ j, N j := by
    apply le_antisymm
    · intro x hx
      apply (Submodule.mem_iInf N).mpr
      intro j
      have hxmax : x ∈ N (max j k₀) := by
        rw [hstable (max j k₀) (le_max_right _ _)]
        exact hx
      exact hN (le_max_left _ _) hxmax
    · exact iInf_le N k₀
  exact ⟨k₀, fun k hk => (hstable k hk).trans hzero⟩

/-- If the full kernels intersect trivially, every finite-dimensional test
subspace is eventually seen injectively by all later quotient maps. -/
theorem eventually_quotient_injective_on_finite_subspace
    (N : ℕ → Submodule K X) (hN : Antitone N) (hsep : (⨅ j, N j) = ⊥)
    (Y : Submodule K X) [FiniteDimensional K Y] :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      Function.Injective (((N k).mkQ).comp Y.subtype) := by
  let F : ℕ → Submodule K Y := fun k => (N k).comap Y.subtype
  have hF : Antitone F := fun _ _ hij => Submodule.comap_mono (hN hij)
  have hsepF : (⨅ j, F j) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    apply Subtype.ext
    have hy' : y.val ∈ ⨅ j, N j := by
      apply (Submodule.mem_iInf N).mpr
      intro j
      exact (Submodule.mem_iInf F).mp hy j
    simpa only [hsep, Submodule.mem_bot] using hy'
  obtain ⟨k₀, hk₀⟩ := antitone_submodules_eventually_eq_iInf F hF
  refine ⟨k₀, ?_⟩
  intro k hk
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  change F k = ⊥
  rw [hk₀ k hk, hsepF]

/-- The linear-algebra dimension step in Theorem C, including arbitrary
infinite-dimensional ambient spaces. A separating antitone sequence of kernels
has a cofinal tail of quotients with dimension larger than the fixed `n`. -/
theorem cofinal_quotient_dimension
    (N : ℕ → Submodule K X) (hN : Antitone N) (hsep : (⨅ j, N j) = ⊥)
    (n : ℕ) (hn : (n : Cardinal) < Module.rank K X) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (n : Cardinal) < Module.rank K (X ⧸ N k) := by
  have hn₁ : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank K X := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Cardinal.natCast_add_one_le_iff.mpr hn)
  obtain ⟨Y, _, hfinite, hdim⟩ :=
    exists_extension_of_finrank_le (K := K) (n + 1) hn₁ (⊥ : Submodule K X) (by simp)
  letI : FiniteDimensional K Y := hfinite
  obtain ⟨k₀, hk₀⟩ := eventually_quotient_injective_on_finite_subspace N hN hsep Y
  refine ⟨k₀, ?_⟩
  intro k hk
  have hrank := (((N k).mkQ).comp Y.subtype).rank_le_of_injective (hk₀ k hk)
  rw [← Module.finrank_eq_rank, hdim] at hrank
  apply Cardinal.natCast_add_one_le_iff.mp
  simpa only [Nat.cast_add, Nat.cast_one] using hrank

end BanachIsometric
