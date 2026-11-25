module

public import RiemannMasullo.ForMathlib.NumberTheory.WeilBound.PlaneCurve
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Weil's bound, V: étale charts of curves

Let `B` be a domain that is étale over `k[t]`, `k` a finite field, and geometrically integral
(`B ⊗_k k̄` a domain). This is what a smooth curve looks like locally. We find inside `B` a
plane model `k[t][y] ≅ k[t][Y]/F` (a primitive element `y` integral over `k[t]`, `F` its minimal
polynomial) with `B[1/s] = k[t][y][1/s]` for some nonzero `s ∈ k[t]`, check the hypotheses of the
plane-curve bound (`weil_planeCurve_aux`) for `F`, and conclude (`weil_etale`):
`#Hom_k(B[1/s], K) = #K + O(√#K)` for finite extensions `K/k` of large degree.
-/

@[expose] public section

open Polynomial

namespace RiemannMasullo.WeilBound

section Denominators

variable {R B : Type*} [CommRing R] [CommRing B] [IsDomain B] [Algebra R B]

/-- A nonzero element `b` of a domain, algebraic over `R`, divides a nonzero element of `R`. -/
theorem exists_dvd_algebraMap {b : B} (hb : b ≠ 0) (halg : IsAlgebraic R b) :
    ∃ r : R, r ≠ 0 ∧ ∃ c : B, algebraMap R B r = b * c := by
  obtain ⟨p, hp0, hp⟩ := halg
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp0 0
  rw [map_zero, sub_zero, X_dvd_iff] at hq
  rw [map_zero, sub_zero] at hpq
  have hq0 : aeval b q = 0 := by
    rw [hpq, map_mul, map_pow, aeval_X] at hp
    exact (mul_eq_zero.1 hp).resolve_left (pow_ne_zero _ hb)
  refine ⟨q.coeff 0, hq, -aeval b q.divX, ?_⟩
  have h := congrArg (aeval b) (X_mul_divX_add q)
  rw [map_add, map_mul, aeval_X, aeval_C, hq0] at h
  rw [mul_neg, eq_neg_iff_add_eq_zero, add_comm]
  exact h


/-- Clearing denominators in a polynomial over the fraction field. -/
theorem exists_clear_denominators [IsDomain R] (p : (FractionRing R)[X]) :
    ∃ r : R, r ≠ 0 ∧ ∃ q : R[X], q.map (algebraMap R (FractionRing R)) = r • p := by
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  exact ⟨b, nonZeroDivisors.ne_zero hb, _, hq⟩

/-- A polynomial that is separable over the fraction field satisfies a Bézout relation
`U F + V F' = r` with `r ≠ 0` over the ring. -/
theorem exists_bezout_of_separable [IsDomain R] {F : R[X]}
    (hsep : (F.map (algebraMap R (FractionRing R))).Separable) :
    ∃ U V : R[X], ∃ r : R, r ≠ 0 ∧ U * F + V * derivative F = C r := by
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨ra, hra, qa, hqa⟩ := exists_clear_denominators a
  obtain ⟨rb, hrb, qb, hqb⟩ := exists_clear_denominators b
  refine ⟨C rb * qa, C ra * qb, ra * rb, mul_ne_zero hra hrb, ?_⟩
  apply Polynomial.map_injective _ (IsFractionRing.injective R (FractionRing R))
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, hqa, hqb, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C,
    ← derivative_map, map_mul]
  rw [← algebraMap_smul (FractionRing R) ra a, ← algebraMap_smul (FractionRing R) rb b,
    smul_eq_C_mul, smul_eq_C_mul]
  have : C (algebraMap R (FractionRing R) rb) * (C (algebraMap R (FractionRing R) ra) * a) *
      F.map (algebraMap R (FractionRing R)) +
      C (algebraMap R (FractionRing R) ra) * (C (algebraMap R (FractionRing R) rb) * b) *
      derivative (F.map (algebraMap R (FractionRing R))) =
      C (algebraMap R (FractionRing R) ra * algebraMap R (FractionRing R) rb) *
        (a * F.map (algebraMap R (FractionRing R)) +
          b * derivative (F.map (algebraMap R (FractionRing R)))) := by
    rw [C_mul]; ring
  rw [this, hab, mul_one]

end Denominators


section EtaleChart

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k[X] B]
  [Algebra.Etale k[X] B]

theorem algebraMap_injective_of_etale : Function.Injective (algebraMap k[X] B) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h0
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) (mem_nonZeroDivisors_of_ne_zero h0)
  apply one_ne_zero (α := B)
  apply hreg
  show r • (1 : B) = r • 0
  rw [smul_zero, Algebra.smul_def, hr, zero_mul]

instance faithfulSMul_of_etale : FaithfulSMul k[X] B :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 algebraMap_injective_of_etale

instance : FaithfulSMul k[X] (FractionRing B) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq k[X] B (FractionRing B)]
    exact (IsFractionRing.injective B _).comp algebraMap_injective_of_etale)

attribute [local instance] FractionRing.liftAlgebra

theorem formallyUnramified_fractionRing :
    Algebra.FormallyUnramified (FractionRing k[X]) (FractionRing B) := by
  have : Algebra.FormallyUnramified k[X] (FractionRing B) :=
    Algebra.FormallyUnramified.comp k[X] B (FractionRing B)
  exact Algebra.FormallyUnramified.of_restrictScalars k[X] _ _

theorem essFiniteType_fractionRing :
    Algebra.EssFiniteType (FractionRing k[X]) (FractionRing B) := by
  have : Algebra.EssFiniteType k[X] (FractionRing B) :=
    Algebra.EssFiniteType.comp k[X] B (FractionRing B)
  exact Algebra.EssFiniteType.of_comp k[X] _ _

theorem finiteDimensional_fractionRing :
    FiniteDimensional (FractionRing k[X]) (FractionRing B) := by
  have := formallyUnramified_fractionRing (k := k) (B := B)
  have := essFiniteType_fractionRing (k := k) (B := B)
  exact Algebra.FormallyUnramified.finite_of_free _ _

theorem isSeparable_fractionRing :
    Algebra.IsSeparable (FractionRing k[X]) (FractionRing B) := by
  have := formallyUnramified_fractionRing (k := k) (B := B)
  have := essFiniteType_fractionRing (k := k) (B := B)
  exact Algebra.FormallyUnramified.isSeparable _ _


theorem isAlgebraic_of_etale (b : B) : IsAlgebraic k[X] b := by
  have := finiteDimensional_fractionRing (k := k) (B := B)
  have h1 : IsAlgebraic (FractionRing k[X]) (algebraMap B (FractionRing B) b) :=
    Algebra.IsAlgebraic.isAlgebraic _
  rw [← IsFractionRing.isAlgebraic_iff k[X] (FractionRing k[X])] at h1
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom k[X] B (FractionRing B))
    (IsFractionRing.injective B _)).1 h1

/-- A primitive element of the function field over `k(t)` that lies in `B` and is integral over
`k[t]`. -/
theorem exists_primitive_integral : ∃ y : B, IsIntegral k[X] y ∧
    IntermediateField.adjoin (FractionRing k[X]) {algebraMap B (FractionRing B) y} = ⊤ := by
  have := finiteDimensional_fractionRing (k := k) (B := B)
  have := isSeparable_fractionRing (k := k) (B := B)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (FractionRing k[X]) (FractionRing B)
  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective B α
  have hb₂0 : b₂ ≠ 0 := nonZeroDivisors.ne_zero hb₂
  obtain ⟨r₁, hr₁, c, hc⟩ := exists_dvd_algebraMap hb₂0 (isAlgebraic_of_etale (k := k) b₂)
  obtain ⟨r₂, hr₂, hint⟩ := (isAlgebraic_of_etale (k := k) (b₁ * c)).exists_integral_multiple
  refine ⟨r₂ • (b₁ * c), hint, ?_⟩
  rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
  set E := FractionRing k[X]
  set L := FractionRing B
  have hb₂L : algebraMap B L b₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).2 hb₂0
  have hr : algebraMap k[X] E (r₂ * r₁) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] E)).2 (mul_ne_zero hr₂ hr₁)
  have key : algebraMap B L (r₂ • (b₁ * c)) =
      algebraMap k[X] E (r₂ * r₁) • (algebraMap B L b₁ / algebraMap B L b₂) := by
    have hcL : algebraMap k[X] L r₁ = algebraMap B L b₂ * algebraMap B L c := by
      rw [IsScalarTower.algebraMap_apply k[X] B L, hc, map_mul]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply k[X] B L, ← IsScalarTower.algebraMap_apply k[X] E L,
      map_mul, hcL]
    field_simp
  have : algebraMap B L b₁ / algebraMap B L b₂ =
      (algebraMap k[X] E (r₂ * r₁))⁻¹ • algebraMap B L (r₂ • (b₁ * c)) := by
    rw [key, smul_smul, inv_mul_cancel₀ hr, one_smul]
  rw [this]
  exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self _ _)


/-- Denominators: some nonzero `s ∈ k[t]` has a power carrying every element of `B` into
`k[t][y]`, `y` a primitive element. -/
theorem exists_denominator {y : B}
    (hy : IntermediateField.adjoin (FractionRing k[X]) {algebraMap B (FractionRing B) y} = ⊤) :
    ∃ s : k[X], s ≠ 0 ∧ ∀ b : B, ∃ m : ℕ,
      algebraMap k[X] B s ^ m * b ∈ Algebra.adjoin k[X] {y} := by
  classical
  have := finiteDimensional_fractionRing (k := k) (B := B)
  set E := FractionRing k[X]
  set L := FractionRing B
  set A₀ := Algebra.adjoin k[X] {y}
  have hden : ∀ b : B, ∃ r : k[X], r ≠ 0 ∧ algebraMap k[X] B r * b ∈ A₀ := by
    intro b
    have hb : algebraMap B L b ∈ (IntermediateField.adjoin E {algebraMap B L y}).toSubalgebra := by
      rw [hy]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨p, hp⟩ := hb
    obtain ⟨r, hr, q, hq⟩ := exists_clear_denominators p
    refine ⟨r, hr, ?_⟩
    have h1 : algebraMap B L (aeval y q) = algebraMap B L (algebraMap k[X] B r * b) := by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp
      rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap E, hq, ← algebraMap_smul E r p,
        smul_eq_C_mul, map_mul, aeval_C, hp, map_mul, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    rw [← IsFractionRing.injective B L h1]
    exact aeval_mem_adjoin_singleton _ _
  choose r hr0 hr using hden
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k[X] B).FG)
  refine ⟨∏ b ∈ t, r b, Finset.prod_ne_zero_iff.2 fun b _ => hr0 b, fun b => ?_⟩
  have hb : b ∈ Algebra.adjoin k[X] (t : Set B) := by rw [ht]; trivial
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨1, ?_⟩
    rw [pow_one, ← Finset.prod_erase_mul t r hx, map_mul, mul_assoc]
    exact A₀.mul_mem (A₀.algebraMap_mem _) (hr x)
  | algebraMap c => exact ⟨0, by simp [A₀.algebraMap_mem c]⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', hm'⟩ := hx'
    refine ⟨m + m', ?_⟩
    have : algebraMap k[X] B (∏ b ∈ t, r b) ^ (m + m') * (x + x') =
        algebraMap k[X] B (∏ b ∈ t, r b) ^ m' * (algebraMap k[X] B (∏ b ∈ t, r b) ^ m * x) +
        algebraMap k[X] B (∏ b ∈ t, r b) ^ m * (algebraMap k[X] B (∏ b ∈ t, r b) ^ m' * x') := by
      ring
    rw [this]
    refine A₀.add_mem (A₀.mul_mem ?_ hm) (A₀.mul_mem ?_ hm')
    · exact A₀.pow_mem (A₀.algebraMap_mem _) _
    · exact A₀.pow_mem (A₀.algebraMap_mem _) _
  | mul x x' _ _ hx hx' =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', hm'⟩ := hx'
    refine ⟨m + m', ?_⟩
    have : algebraMap k[X] B (∏ b ∈ t, r b) ^ (m + m') * (x * x') =
        (algebraMap k[X] B (∏ b ∈ t, r b) ^ m * x) *
        (algebraMap k[X] B (∏ b ∈ t, r b) ^ m' * x') := by ring
    rw [this]
    exact A₀.mul_mem hm hm'

end EtaleChart


section BaseChangeDomain

open scoped TensorProduct

variable {k : Type*} [Field k] {F : k[X][X]} (hF : F.Monic) (L : Type*) [Field L] [Algebra k L]

/-- The comparison `L[t][Y]/F → L ⊗_k (k[t][Y]/F)`; it sends the monomial basis to the
base-changed monomial basis. -/
noncomputable def toTensor : AdjoinRoot (baseChange L F) →ₐ[L] L ⊗[k] AdjoinRoot F :=
  AdjoinRoot.liftAlgHom _ (aeval ((1 : L) ⊗ₜ[k] AdjoinRoot.of F X))
    ((1 : L) ⊗ₜ[k] AdjoinRoot.root F) (by
      have hcomp : RingHom.comp ((aeval ((1 : L) ⊗ₜ[k] AdjoinRoot.of F X) :
          L[X] →ₐ[L] L ⊗[k] AdjoinRoot F) : L[X] →+* L ⊗[k] AdjoinRoot F)
          (mapRingHom (algebraMap k L)) =
          RingHom.comp ((Algebra.TensorProduct.includeRight (R := k) (A := L)
            (B := AdjoinRoot F)) : AdjoinRoot F →+* L ⊗[k] AdjoinRoot F) (AdjoinRoot.of F) := by
        apply Polynomial.ringHom_ext
        · intro a
          have e1 : AdjoinRoot.of F (C a) = algebraMap k (AdjoinRoot F) a := by
            rw [IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot F), AdjoinRoot.algebraMap_eq]
            rfl
          simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, Polynomial.map_C,
            RingHom.coe_coe, aeval_C, Algebra.TensorProduct.includeRight_apply, e1,
            Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := AdjoinRoot F),
            TensorProduct.smul_tmul]
        · simp
      rw [baseChange, eval₂_map, hcomp]
      have := hom_eval₂ F (AdjoinRoot.of F) ((Algebra.TensorProduct.includeRight (R := k) (A := L)
        (B := AdjoinRoot F)) : AdjoinRoot F →+* L ⊗[k] AdjoinRoot F) (AdjoinRoot.root F)
      rw [AdjoinRoot.eval₂_root, map_zero] at this
      exact this.symm)


include hF in
theorem toTensor_monoBasis (l : ℕ × Fin (baseChange L F).natDegree) :
    toTensor L (F := F) (monoBasis (baseChange_monic L hF) l) =
      Algebra.TensorProduct.basis L (monoBasis hF) (l.1, Fin.cast (natDegree_baseChange L hF) l.2) := by
  simp only [monoBasis_apply, Algebra.TensorProduct.basis_apply, map_mul, map_pow, toTensor,
    AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root, aeval_X,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul]
  rfl

include hF in
theorem toTensor_injective : Function.Injective (toTensor L (F := F)) := by
  have hF' := baseChange_monic L hF
  have hdeg := natDegree_baseChange L hF
  let e : ℕ × Fin (baseChange L F).natDegree → ℕ × Fin F.natDegree :=
    fun l => (l.1, Fin.cast hdeg l.2)
  have he : Function.Injective e := by
    intro l l' hll'
    simp only [e, Prod.mk.injEq] at hll'
    exact Prod.ext hll'.1 (Fin.cast_injective _ hll'.2)
  apply LinearMap.injective_of_linearIndependent (f := (toTensor L (F := F)).toLinearMap)
    (v := monoBasis hF') (monoBasis hF').span_eq
  have : (toTensor L (F := F)).toLinearMap ∘ monoBasis hF' =
      Algebra.TensorProduct.basis L (monoBasis hF) ∘ e := by
    funext l
    exact toTensor_monoBasis hF L l
  rw [this]
  exact (Algebra.TensorProduct.basis L (monoBasis hF)).linearIndependent.comp e he

include hF in
/-- **Geometric integrality transfers to the plane model.** If `k[t][Y]/F` embeds into a
`k`-algebra `B` with `L ⊗_k B` a domain, then `L[t][Y]/F` is a domain. -/
theorem isDomain_adjoinRoot_baseChange {B : Type*} [CommRing B] [Algebra k B]
    (j : AdjoinRoot F →ₐ[k] B) (hj : Function.Injective j) [IsDomain (L ⊗[k] B)] :
    IsDomain (AdjoinRoot (baseChange L F)) := by
  let T := Algebra.TensorProduct.map (AlgHom.id L L) j
  have hT : Function.Injective T := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L) j.toLinearMap hj
    have : (T : L ⊗[k] AdjoinRoot F → L ⊗[k] B) = j.toLinearMap.lTensor L := by
      funext x
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp [T]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [this]; exact h
  exact (hT.comp (toTensor_injective hF L)).isDomain (T.comp (toTensor L)).toRingHom

end BaseChangeDomain


section LocalizationCount

/-- **Comparison of points through a localization.** If `j : A → B` is injective and every element
of `B` becomes, after multiplication by a power of `j s`, an element of `j A`, then the points of
`B[1/s]` with values in a field are the points of `A` where `s` does not vanish. -/
theorem card_algHom_localization_eq {k A B M : Type*} [Field k] [CommRing A] [CommRing B]
    [IsDomain B] [Algebra k A] [Algebra k B] (j : A →ₐ[k] B) (hj : Function.Injective j) (s : A)
    (hs0 : j s ≠ 0) (hden : ∀ b : B, ∃ m : ℕ, ∃ a : A, j s ^ m * b = j a)
    [Field M] [Algebra k M] :
    Nat.card (Localization.Away (j s) →ₐ[k] M) = Nat.card {ψ : A →ₐ[k] M // ψ s ≠ 0} := by
  classical
  set Loc := Localization.Away (j s)
  let : Algebra A Loc := ((algebraMap B Loc).comp j.toRingHom).toAlgebra
  have halg : ∀ a, algebraMap A Loc a = algebraMap B Loc (j a) := fun _ => rfl
  have hinjB : Function.Injective (algebraMap B Loc) :=
    IsLocalization.injective Loc (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  have hloc : IsLocalization.Away s Loc := by
    unfold IsLocalization.Away
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      rw [map_pow, halg]
      exact (IsLocalization.Away.algebraMap_isUnit (j s)).pow n
    · intro z
      obtain ⟨⟨b, _, n, rfl⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (j s)) z
      obtain ⟨m, a, ha⟩ := hden b
      refine ⟨⟨a, ⟨s ^ (m + n), ⟨m + n, rfl⟩⟩⟩, ?_⟩
      simp only [halg, map_pow]
      rw [← ha, map_mul, ← hz, map_pow, map_pow, pow_add]
      ring
    · intro x y hxy
      exact ⟨1, by rw [hj (hinjB hxy)]⟩
  have hunit : ∀ ψ : A →ₐ[k] M, ψ s ≠ 0 → IsUnit ((ψ : A →+* M) s) :=
    fun ψ h => isUnit_iff_ne_zero.2 h
  let toFun : (Loc →ₐ[k] M) → {ψ : A →ₐ[k] M // ψ s ≠ 0} := fun φ =>
    ⟨(φ.comp (IsScalarTower.toAlgHom k B Loc)).comp j, by
      intro h
      have hu : IsUnit (algebraMap B Loc (j s)) := IsLocalization.Away.algebraMap_isUnit (j s)
      have := hu.map φ
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h
      rw [h] at this
      exact not_isUnit_zero this⟩
  let invFun : {ψ : A →ₐ[k] M // ψ s ≠ 0} → (Loc →ₐ[k] M) := fun ψ =>
    { IsLocalization.Away.lift s (hunit ψ.1 ψ.2) with
      commutes' := fun c => by
        have : algebraMap k Loc c = algebraMap A Loc (algebraMap k A c) := by
          rw [halg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_ofClass]
        rw [this, IsLocalization.Away.lift_eq]
        simp }
  have e : (Loc →ₐ[k] M) ≃ {ψ : A →ₐ[k] M // ψ s ≠ 0} :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun φ => by
        apply AlgHom.toRingHom_injective
        apply IsLocalization.ringHom_ext (Submonoid.powers s)
        ext a
        simp [invFun, toFun, halg]
      right_inv := fun ψ => by
        apply Subtype.ext
        ext a
        simp only [toFun, invFun, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
        rw [← halg]
        exact IsLocalization.Away.lift_eq s (hunit ψ.1 ψ.2) a }
  exact Nat.card_congr e

end LocalizationCount


section FiniteFieldPoints

/-- The points of `k[t][Y]/F` with values in a finite field `K` with `Q` elements are the points
with values in an algebraic closure whose coordinates are fixed by `x ↦ x ^ Q`. -/
theorem card_algHom_finiteField_eq {k : Type*} [Field k] (F : k[X][X])
    (K : Type*) [Field K] [Fintype K] [Algebra k K]
    (L : Type*) [Field L] [IsAlgClosed L] [Algebra k L] :
    Nat.card (AdjoinRoot F →ₐ[k] K) = {φ : AdjoinRoot F →ₐ[k] L |
        φ (AdjoinRoot.of F X) ^ Fintype.card K = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ Fintype.card K = φ (AdjoinRoot.root F)}.ncard := by
  classical
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let σ : K →ₐ[k] L := IsAlgClosed.lift
  have hσ : Function.Injective σ := σ.toRingHom.injective
  have hQ1 : 1 < Fintype.card K := Fintype.one_lt_card
  -- the image of `σ` is the set of solutions of `z ^ Fintype.card K = z`
  have himage : ∀ z : L, z ^ Fintype.card K = z → ∃ a : K, σ a = z := by
    intro z hz
    set G : L[X] := X ^ Fintype.card K - X
    have hG0 : G ≠ 0 := by
      intro h
      have := natDegree_X_pow_sub_X (R := L) hQ1
      rw [← show G = X ^ Fintype.card K - X from rfl, h, natDegree_zero] at this
      omega
    have hsub : Finset.univ.image σ ⊆ G.roots.toFinset := by
      intro w hw
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hw
      rw [Multiset.mem_toFinset, mem_roots hG0, IsRoot.def]
      simp only [G, eval_sub, eval_pow, eval_X, ← map_pow, FiniteField.pow_card, sub_self]
    have hcard : G.roots.toFinset.card ≤ (Finset.univ.image σ).card := by
      rw [Finset.card_image_of_injective _ hσ, Finset.card_univ]
      calc G.roots.toFinset.card ≤ G.roots.card := Multiset.toFinset_card_le _
        _ ≤ G.natDegree := card_roots' _
        _ = Fintype.card K := natDegree_X_pow_sub_X hQ1
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hz' : z ∈ G.roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots hG0, IsRoot.def]
      simp [G, hz]
    rw [← heq] at hz'
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hz'
    exact ⟨a, ha⟩
  have hof : ∀ φ : AdjoinRoot F →ₐ[k] L,
      φ.comp (AdjoinRoot.ofAlgHom k F) = aeval (φ (AdjoinRoot.of F X)) := by
    intro φ
    apply Polynomial.algHom_ext
    simp
  let Φ : (AdjoinRoot F →ₐ[k] K) → {φ : AdjoinRoot F →ₐ[k] L |
      φ (AdjoinRoot.of F X) ^ Fintype.card K = φ (AdjoinRoot.of F X) ∧
      φ (AdjoinRoot.root F) ^ Fintype.card K = φ (AdjoinRoot.root F)} := fun ψ =>
    ⟨σ.comp ψ, ⟨by rw [AlgHom.comp_apply, ← map_pow, FiniteField.pow_card],
      by rw [AlgHom.comp_apply, ← map_pow, FiniteField.pow_card]⟩⟩
  have hΦinj : Function.Injective Φ := by
    intro ψ ψ' h
    apply AlgHom.ext
    intro x
    have := congrArg (fun φ => (φ : AdjoinRoot F →ₐ[k] L) x) (congrArg Subtype.val h)
    exact hσ this
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨φ, ht, hy⟩
    obtain ⟨a, ha⟩ := himage _ ht
    obtain ⟨b, hb⟩ := himage _ hy
    have hroot : F.eval₂ ((aeval a : k[X] →ₐ[k] K) : k[X] →+* K) b = 0 := by
      apply hσ
      have e1 : ((σ : K →+* L).comp ((aeval a : k[X] →ₐ[k] K) : k[X] →+* K)) =
          ((φ : AdjoinRoot F →+* L).comp (AdjoinRoot.of F)) := by
        apply Polynomial.ringHom_ext
        · intro c
          have : AdjoinRoot.of F (C c) = algebraMap k (AdjoinRoot F) c := by
            rw [IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot F), AdjoinRoot.algebraMap_eq]
            rfl
          simp [this]
        · simp [ha]
      have e2 := hom_eval₂ F ((aeval a : k[X] →ₐ[k] K) : k[X] →+* K) (σ : K →+* L) b
      have e3 := hom_eval₂ F (AdjoinRoot.of F) (φ : AdjoinRoot F →+* L) (AdjoinRoot.root F)
      rw [AdjoinRoot.eval₂_root, map_zero] at e3
      rw [map_zero]
      simp only [RingHom.coe_coe] at e2 e3
      rw [e2, e1, hb, ← e3]
    refine ⟨AdjoinRoot.liftAlgHom F (aeval a) b hroot, ?_⟩
    apply Subtype.ext
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      show σ (AdjoinRoot.liftAlgHom F (aeval a) b hroot (AdjoinRoot.of F X)) = φ (AdjoinRoot.of F X)
      rw [AdjoinRoot.liftAlgHom_of, aeval_X, ha]
    · show σ (AdjoinRoot.liftAlgHom F (aeval a) b hroot (AdjoinRoot.root F)) = φ (AdjoinRoot.root F)
      rw [AdjoinRoot.liftAlgHom_root, hb]
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩)

end FiniteFieldPoints


section EtaleMain

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra

/-- **Weil's bound on an étale chart.** Let `B` be a domain, étale over `k[t]` (`k` finite), and
geometrically integral (`B ⊗_k k̄` is a domain). Then for some nonzero `s ∈ k[t]` the number of
points of `B[1/s]` with values in a finite extension `K` of `k` is `#K + O(√#K)`. -/
theorem weil_etale {k : Type*} [Field k] [Fintype k] {B : Type*} [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra k[X] B] [IsScalarTower k k[X] B] [Algebra.Etale k[X] B]
    [IsDomain (B ⊗[k] AlgebraicClosure k)] :
    ∃ s : k[X], s ≠ 0 ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ (K : Type*) [Field K] [Algebra k K] [Fintype K],
      n₀ ≤ Module.finrank k K →
      |(Nat.card (Localization.Away (algebraMap k[X] B s) →ₐ[k] K) : ℝ) - Fintype.card K| ≤
        C * Real.sqrt (Fintype.card K) := by
  classical
  set L := AlgebraicClosure k
  obtain ⟨y, hint, hprim⟩ := exists_primitive_integral (k := k) (B := B)
  set F := minpoly k[X] y with hF_def
  have hF : F.Monic := minpoly.monic hint
  have hd : 0 < F.natDegree := minpoly.natDegree_pos hint
  let j₀ : AdjoinRoot F →ₐ[k[X]] B :=
    (Algebra.adjoin k[X] {y}).val.comp (minpoly.equivAdjoin hint).toAlgHom
  have hj₀ : Function.Injective j₀ :=
    Subtype.val_injective.comp (minpoly.equivAdjoin hint).injective
  let j : AdjoinRoot F →ₐ[k] B := j₀.restrictScalars k
  have hj : Function.Injective j := hj₀
  have hj_of : ∀ p, j (AdjoinRoot.of F p) = algebraMap k[X] B p := fun p => by
    show j₀ (AdjoinRoot.of F p) = _
    rw [← AdjoinRoot.algebraMap_eq, AlgHom.commutes]
  have hrange : ∀ b ∈ Algebra.adjoin k[X] {y}, ∃ a, j a = b := by
    intro b hb
    obtain ⟨a, ha⟩ := (minpoly.equivAdjoin hint).surjective ⟨b, hb⟩
    exact ⟨a, by
      show (((minpoly.equivAdjoin hint) a : Algebra.adjoin k[X] {y}) : B) = b
      rw [ha]⟩
  obtain ⟨s, hs0, hden⟩ := exists_denominator hprim
  have hdomA : IsDomain (AdjoinRoot F) := hj₀.isDomain j₀.toRingHom
  obtain ⟨w, hw⟩ := exists_weight F
  -- separability
  have hsep : (F.map (algebraMap k[X] (FractionRing k[X]))).Separable := by
    have := isSeparable_fractionRing (k := k) (B := B)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions (FractionRing k[X]) (FractionRing B) hint]
    exact Algebra.IsSeparable.isSeparable _ _
  obtain ⟨U, V, r, hr, hUV⟩ := exists_bezout_of_separable hsep
  -- geometric integrality of the plane model
  have hLB : IsDomain (L ⊗[k] B) :=
    MulEquiv.isDomain (B ⊗[k] L) (Algebra.TensorProduct.comm k L B).toMulEquiv
  have hirr : IsDomain (AdjoinRoot (baseChange L F)) :=
    isDomain_adjoinRoot_baseChange hF L j hj
  obtain ⟨C, n₀, hW⟩ := weil_planeCurve_aux hF hd L hr hUV
  set q := Fintype.card k
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Fintype.card_pos
  set C₀ : ℕ := F.natDegree * s.natDegree + w * F.natDegree * F.natDegree
  refine ⟨s, hs0, C * Real.sqrt q + C₀, n₀, fun K _ _ _ hK => ?_⟩
  set n := Module.finrank k K
  have hcardK : Fintype.card K = q ^ n := by
    have : Module.Finite k K := Module.Finite.of_finite
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card]
  -- the localization
  have hs' : j (AdjoinRoot.of F s) ≠ 0 := by
    rw [hj_of]
    exact (map_ne_zero_iff _ algebraMap_injective_of_etale).2 hs0
  have hden' : ∀ b : B, ∃ m : ℕ, ∃ a : AdjoinRoot F, j (AdjoinRoot.of F s) ^ m * b = j a := by
    intro b
    obtain ⟨m, hm⟩ := hden b
    obtain ⟨a, ha⟩ := hrange _ hm
    exact ⟨m, a, by rw [hj_of, ha]⟩
  have h1 := card_algHom_localization_eq j hj (AdjoinRoot.of F s) hs' hden' (M := K)
  rw [hj_of] at h1
  -- the bad points
  have hs0A : AdjoinRoot.of F s ≠ 0 := fun h => hs' (by rw [h, map_zero])
  obtain ⟨hbadfin, hbad⟩ :=
    card_algHom_apply_eq_zero_le hF hw K (of_mem_filt hF hw s) hs0A
  -- all points
  have hfinA : Finite (AdjoinRoot F →ₐ[k] K) := by
    refine Finite.of_injective (fun ψ : AdjoinRoot F →ₐ[k] K =>
      (ψ (AdjoinRoot.of F X), ψ (AdjoinRoot.root F))) ?_
    intro ψ ψ' h
    simp only [Prod.mk.injEq] at h
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      exact h.1
    · exact h.2
  have hsplit : Nat.card {ψ : AdjoinRoot F →ₐ[k] K // ψ (AdjoinRoot.of F s) ≠ 0} +
      Nat.card {ψ : AdjoinRoot F →ₐ[k] K // ψ (AdjoinRoot.of F s) = 0} =
      Nat.card (AdjoinRoot F →ₐ[k] K) := by
    have := Fintype.ofFinite (AdjoinRoot F →ₐ[k] K)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le (fun ψ : AdjoinRoot F →ₐ[k] K => ψ (AdjoinRoot.of F s) = 0)
    omega
  have h2 := card_algHom_finiteField_eq F K L
  rw [hcardK] at h2
  obtain ⟨-, hW'⟩ := hW n hK
  rw [← h2] at hW'
  -- arithmetic
  set NA := Nat.card (AdjoinRoot F →ₐ[k] K)
  set Ngood := Nat.card {ψ : AdjoinRoot F →ₐ[k] K // ψ (AdjoinRoot.of F s) ≠ 0}
  set Nbad := Nat.card {ψ : AdjoinRoot F →ₐ[k] K // ψ (AdjoinRoot.of F s) = 0}
  have hW'' : |(NA : ℝ) - (q : ℝ) ^ n| ≤ C * (q : ℝ) ^ (n - n / 2) := by
    have : ((|(NA : ℤ) - (q : ℤ) ^ n| : ℤ) : ℝ) ≤ ((C * (q : ℤ) ^ (n - n / 2) : ℤ) : ℝ) := by
      exact_mod_cast hW'
    push_cast at this
    exact this
  have hq1' : (q : ℝ) ^ (n - n / 2) ≤ Real.sqrt q * Real.sqrt ((q : ℝ) ^ n) := by
    rw [← Real.sqrt_mul (by positivity), ← pow_succ']
    have h3 : (q : ℝ) ^ (n - n / 2) = Real.sqrt (((q : ℝ) ^ (n - n / 2)) ^ 2) :=
      (Real.sqrt_sq (by positivity)).symm
    rw [h3]
    apply Real.sqrt_le_sqrt
    rw [← pow_mul]
    exact pow_le_pow_right₀ hq1 (by omega)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((q : ℝ) ^ n) := by
    rw [Real.one_le_sqrt]; exact one_le_pow₀ hq1
  have hC0 : (0 : ℝ) ≤ C := by positivity
  rw [h1, hcardK]
  push_cast
  have hsplit' : (Ngood : ℝ) = NA - Nbad := by
    rw [← hsplit]; push_cast; ring
  have hbad' : (Nbad : ℝ) ≤ C₀ := by exact_mod_cast hbad
  have hbad0 : (0 : ℝ) ≤ Nbad := by positivity
  rw [hsplit']
  calc |(NA : ℝ) - Nbad - (q : ℝ) ^ n| ≤ |(NA : ℝ) - (q : ℝ) ^ n| + Nbad := by
        rw [show (NA : ℝ) - Nbad - (q : ℝ) ^ n = ((NA : ℝ) - (q : ℝ) ^ n) + (-Nbad) by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_of_nonneg hbad0]
    _ ≤ C * (q : ℝ) ^ (n - n / 2) + C₀ := add_le_add hW'' hbad'
    _ ≤ C * (Real.sqrt q * Real.sqrt ((q : ℝ) ^ n)) + C₀ * Real.sqrt ((q : ℝ) ^ n) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) hsqrt1
    _ = (C * Real.sqrt q + C₀) * Real.sqrt ((q : ℝ) ^ n) := by ring

end EtaleMain

end RiemannMasullo.WeilBound
