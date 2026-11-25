module

public import RiemannMasullo.ForMathlib.NumberTheory.WeilBound.Filtration
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Weil's bound, II: Bombieri's non-cancellation lemma

Bombieri's proof of Weil's bound needs, for `q₁` a power of `#k` large compared with `a`, that the
`q₁`-th powers of distinct monomials are linearly independent over the elements of weight `≤ a`
(`nonCancellation`). Bombieri uses pole orders at a rational point; a rational point need not
exist over `k`, so we use instead a point over an extension `L` (for instance an algebraic
closure) and the expansion of the curve there:

* `exists_algHom_powerSeries`: a simple root `η` of `F(c, Y)` gives, by Hensel's lemma, an
  `L`-algebra map `ψ : L[t][Y]/F → L⟦T⟧` with `ψ t = c + T`;
* `not_X_pow_dvd`: when `L[t][Y]/F` is a domain (the curve is irreducible over `L`), a nonzero
  element of weight `≤ a` has order `≤ d a + w d²` at `T = 0`; in particular `ψ` is injective;
* `eq_zero_of_sum_mul_pow_eq_zero`: the power series form of non-cancellation.
-/

@[expose] public section

open scoped PowerSeries

namespace RiemannMasullo.WeilBound

section PowerSeriesLemma

open PowerSeries


/-- Bombieri's non-cancellation in a power series ring. Let `N` be a power of the characteristic
(so that `x ↦ x ^ N` is additive). If the `L`-span of `v i` (`i ∈ s`) meets `X ^ N L⟦X⟧` only
in `0` (with independent coefficients), then `∑ v i * P i ^ N = 0` forces every `P i = 0`. -/
theorem eq_zero_of_sum_mul_pow_eq_zero {L : Type*} [Field L] {N : ℕ} (hN : 0 < N)
    (hadd : ∀ a b : L⟦X⟧, (a + b) ^ N = a ^ N + b ^ N)
    {ι : Type*} (s : Finset ι) (v P : ι → L⟦X⟧)
    (hv : ∀ c : ι → L, (X : L⟦X⟧) ^ N ∣ ∑ i ∈ s, C (c i) * v i → ∀ i ∈ s, c i = 0)
    (h : ∑ i ∈ s, v i * P i ^ N = 0) : ∀ i ∈ s, P i = 0 := by
  have key : ∀ m : ℕ, ∀ i ∈ s, (X : L⟦X⟧) ^ m ∣ P i := by
    intro m
    induction m with
    | zero => intro i _; simp
    | succ m ih =>
      choose! R hR using ih
      -- `P i = X ^ m * R i`
      have h1 : ∑ i ∈ s, v i * R i ^ N = 0 := by
        have : (X : L⟦X⟧) ^ (m * N) * ∑ i ∈ s, v i * R i ^ N = 0 := by
          rw [← h, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hR i hi, mul_pow, ← pow_mul]; ring
        exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ X_ne_zero)
      -- split off constant coefficients
      set S : L⟦X⟧ → L⟦X⟧ := fun φ => mk fun p => coeff (p + 1) φ
      have hsplit : ∀ i, R i ^ N = C (constantCoeff (R i) ^ N) + X ^ N * S (R i) ^ N := by
        intro i
        conv_lhs => rw [eq_X_mul_shift_add_const (R i)]
        rw [hadd, mul_pow, map_pow, add_comm]
      have h2 : (X : L⟦X⟧) ^ N ∣ ∑ i ∈ s, C (constantCoeff (R i) ^ N) * v i := by
        refine ⟨-∑ i ∈ s, v i * S (R i) ^ N, ?_⟩
        have : ∑ i ∈ s, v i * R i ^ N = ∑ i ∈ s, C (constantCoeff (R i) ^ N) * v i +
            X ^ N * ∑ i ∈ s, v i * S (R i) ^ N := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsplit]; ring
        rw [h1] at this
        linear_combination -this
      have h3 := hv _ h2
      intro i hi
      have h4 : constantCoeff (R i) = 0 := pow_eq_zero_iff hN.ne' |>.1 (h3 i hi)
      obtain ⟨T, hT⟩ := X_dvd_iff.2 h4
      exact ⟨T, by rw [hR i hi, hT, pow_succ, mul_assoc]⟩
  intro i hi
  ext n
  have := X_pow_dvd_iff.1 (key (n + 1) i hi) n (Nat.lt_succ_self n)
  simpa using this


end PowerSeriesLemma

open Polynomial


section Expansion

variable {L : Type*} [Field L] {F : L[X][X]} (hF : F.Monic)

theorem constantCoeff_comp_aeval (c : L) :
    (PowerSeries.constantCoeff (R := L)).comp
      (aeval (PowerSeries.C c + PowerSeries.X : L⟦X⟧)).toRingHom = evalRingHom c := by
  apply Polynomial.ringHom_ext
  · intro a; simp
  · simp

include hF in
/-- A simple root `η` of `F(c, Y)` lifts to a power series root of `F(c + T, Y)`: the expansion
of the curve `F = 0` at the point `(c, η)`. -/
theorem exists_algHom_powerSeries (c η : L) (h0 : (F.map (evalRingHom c)).eval η = 0)
    (h1 : (F.map (evalRingHom c)).derivative.eval η ≠ 0) :
    ∃ ψ : AdjoinRoot F →ₐ[L] L⟦X⟧,
      ψ (AdjoinRoot.of F X) = PowerSeries.C c + PowerSeries.X := by
  set i : L[X] →ₐ[L] L⟦X⟧ := aeval (PowerSeries.C c + PowerSeries.X)
  set f : L⟦X⟧[X] := F.map i.toRingHom
  have hf : f.Monic := hF.map _
  have hcc : (PowerSeries.constantCoeff (R := L)).comp i.toRingHom = evalRingHom c :=
    constantCoeff_comp_aeval c
  have e0 : PowerSeries.constantCoeff (f.eval (PowerSeries.C η)) =
      (F.map (evalRingHom c)).eval η := by
    rw [← eval_map_apply, Polynomial.map_map, hcc]; simp
  have e1 : PowerSeries.constantCoeff (f.derivative.eval (PowerSeries.C η)) =
      (F.map (evalRingHom c)).derivative.eval η := by
    rw [← eval_map_apply, derivative_map, Polynomial.map_map, hcc, derivative_map]; simp
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian (I := Ideal.span {PowerSeries.X}) f hf
    (PowerSeries.C η)
    (by rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, e0, h0])
    (by
      apply IsUnit.map
      rw [PowerSeries.isUnit_iff_constantCoeff, e1]
      exact h1.isUnit)
  refine ⟨AdjoinRoot.liftAlgHom F i y ?_, ?_⟩
  · rw [← eval_map]; exact hy
  · simp [i]


variable {w : ℕ} (hw : ∀ i < F.natDegree, (F.coeff i).natDegree ≤ (F.natDegree - i) * w)
include hF hw

/-- The order bound: under an expansion `ψ` with `ψ t = c + T`, a nonzero `u` of weight `≤ a`
vanishes at `T = 0` to order `≤ d a + w d²` (its order is at most `dim A / u A`). -/
theorem not_X_pow_dvd [IsDomain (AdjoinRoot F)] (ψ : AdjoinRoot F →ₐ[L] L⟦X⟧) (c : L)
    (hψ : ψ (AdjoinRoot.of F X) = PowerSeries.C c + PowerSeries.X) {u : AdjoinRoot F} {a : ℕ}
    (hu : u ∈ filt hF w a) (hu0 : u ≠ 0) :
    ¬ (PowerSeries.X : L⟦X⟧) ^ (F.natDegree * a + w * F.natDegree * F.natDegree + 1) ∣ ψ u := by
  intro hdvd
  set m := F.natDegree * a + w * F.natDegree * F.natDegree + 1 with hm
  let Λ : AdjoinRoot F →ₗ[L] (Fin m → L) :=
    LinearMap.pi fun i => (PowerSeries.coeff (i : ℕ)) ∘ₗ ψ.toLinearMap
  have hΛ : ∀ x, Λ (u * x) = 0 := by
    intro x
    funext i
    simp only [Λ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, map_mul, Pi.zero_apply]
    exact PowerSeries.X_pow_dvd_iff.1 (dvd_mul_of_dvd_left hdvd _) i i.2
  have hT : ψ (AdjoinRoot.of F (X - C c)) = PowerSeries.X := by
    have e : AdjoinRoot.of F (C c) = algebraMap L (AdjoinRoot F) c := by
      rw [IsScalarTower.algebraMap_apply L L[X] (AdjoinRoot F), Polynomial.algebraMap_eq,
        AdjoinRoot.algebraMap_eq]
    rw [map_sub, map_sub, hψ, e, AlgHom.commutes]
    simp
  have hx : ∀ i : Fin m, (AdjoinRoot.of F (X - C c)) ^ (i : ℕ) ∈ filt hF w (a + m) := by
    intro i
    have h1 := pow_mem_filt hF hw (of_mem_filt hF hw (X - C c)) i
    rw [natDegree_X_sub_C, mul_one] at h1
    exact filt_mono hF w (by omega) h1
  have hΛx : ∀ i : Fin m, Λ ((AdjoinRoot.of F (X - C c)) ^ (i : ℕ)) = Pi.single i 1 := by
    intro i
    funext j
    simp only [Λ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, map_pow, hT, PowerSeries.coeff_X_pow]
    by_cases hij : j = i
    · subst hij; simp
    · rw [Pi.single_eq_of_ne hij, ite_eq_right_iff.2 (fun h => absurd (Fin.ext h) hij)]
  have hle : (⊤ : Submodule L (Fin m → L)) ≤ (filt hF w (a + m)).map Λ := by
    rw [← (Pi.basisFun L (Fin m)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, hx i, by rw [hΛx]; simp⟩
  have h1 := Submodule.finrank_mono hle
  rw [finrank_top, Module.finrank_fin_fun] at h1
  have h2 := finrank_map_filt_le hF hw Λ hu hu0 hΛ (N := a + m) (by omega)
  omega

/-- An expansion `ψ` with `ψ t = c + T` is injective. -/
theorem injective_of_expansion [IsDomain (AdjoinRoot F)] (ψ : AdjoinRoot F →ₐ[L] L⟦X⟧) (c : L)
    (hψ : ψ (AdjoinRoot.of F X) = PowerSeries.C c + PowerSeries.X) : Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  obtain ⟨n, hn⟩ := exists_mem_filt hF w x
  exact not_X_pow_dvd hF hw ψ c hψ hn hx0 (by rw [hx]; exact dvd_zero _)

end Expansion


section BaseChange

variable {k : Type*} [Field k] (L : Type*) [Field L] [Algebra k L] {F : k[X][X]} (hF : F.Monic)

/-- `F` with coefficients mapped to `L`. -/
noncomputable abbrev baseChange (L : Type*) [Field L] [Algebra k L] (F : k[X][X]) : L[X][X] :=
  F.map (mapRingHom (algebraMap k L))

include hF in
theorem baseChange_monic : (baseChange L F).Monic := hF.map _

include hF in
theorem natDegree_baseChange : (baseChange L F).natDegree = F.natDegree :=
  hF.natDegree_map _

variable (F) in
/-- The base change map `k[t][Y]/F → L[t][Y]/F`. -/
noncomputable def ι : AdjoinRoot F →ₐ[k] AdjoinRoot (baseChange L F) :=
  { AdjoinRoot.map (mapRingHom (algebraMap k L)) F (baseChange L F) dvd_rfl with
    commutes' := fun a => by
      rw [IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot F),
        IsScalarTower.algebraMap_apply k L[X] (AdjoinRoot (baseChange L F)),
        AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq]
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_ofClass, AdjoinRoot.map_of, coe_mapRingHom, Polynomial.algebraMap_apply]
      simp [Polynomial.map_C] }

theorem ι_of (p : k[X]) : ι L F (AdjoinRoot.of F p) =
    AdjoinRoot.of (baseChange L F) (p.map (algebraMap k L)) := by
  simp [ι]

theorem ι_root : ι L F (AdjoinRoot.root F) = AdjoinRoot.root (baseChange L F) := by
  simp [ι]

theorem ι_monoBasis (l : ℕ × Fin F.natDegree) :
    ι L F (monoBasis hF l) = monoBasis (baseChange_monic L hF)
      (l.1, Fin.cast (natDegree_baseChange L hF).symm l.2) := by
  rw [monoBasis_apply, monoBasis_apply, map_mul, ι_of, map_pow, ι_root, Polynomial.map_pow,
    Polynomial.map_X]
  rfl

include hF in
theorem baseChange_hw {w : ℕ} (hw : ∀ i < F.natDegree, (F.coeff i).natDegree ≤ (F.natDegree - i) * w) :
    ∀ i < (baseChange L F).natDegree,
      ((baseChange L F).coeff i).natDegree ≤ ((baseChange L F).natDegree - i) * w := by
  intro i hi
  rw [natDegree_baseChange L hF] at hi ⊢
  rw [coeff_map, coe_mapRingHom]
  exact (natDegree_map_le).trans (hw i hi)

end BaseChange

theorem frobeniusAlgHom_pow_apply {k R : Type*} [Field k] [Fintype k] [CommRing R] [Algebra k R]
    (m : ℕ) (z : R) : (FiniteField.frobeniusAlgHom k R ^ m) z = z ^ (Fintype.card k ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.frobeniusAlgHom_apply, ← pow_mul, pow_succ]

section NonCancellation

variable {k : Type*} [Field k] [Fintype k] {L : Type*} [Field L] [Algebra k L]
  {F : k[X][X]} (hF : F.Monic) {w : ℕ}
  (hw : ∀ i < F.natDegree, (F.coeff i).natDegree ≤ (F.natDegree - i) * w)

include hF hw in
/-- **Bombieri's non-cancellation lemma.** Suppose that `F` stays a domain over `L` and the curve
has an expansion `ψ` at a point over `L`. If `d a + w d² < q₁ = (#k) ^ m`, then the monomials
`(t ^ j y ^ i) ^ q₁` are linearly independent over the weight-`≤ a` part `filt w a`:
`∑ f_g g ^ q₁ = 0` with `f_g ∈ filt w a` forces every `f_g = 0`. -/
theorem nonCancellation [IsDomain (AdjoinRoot (baseChange L F))]
    (ψ : AdjoinRoot (baseChange L F) →ₐ[L] L⟦X⟧) (c : L)
    (hψ : ψ (AdjoinRoot.of _ X) = PowerSeries.C c + PowerSeries.X)
    {a m : ℕ} (ha : F.natDegree * a + w * F.natDegree * F.natDegree < Fintype.card k ^ m)
    (G : Finset (ℕ × Fin F.natDegree)) (f : ℕ × Fin F.natDegree → AdjoinRoot F)
    (hf : ∀ g ∈ G, f g ∈ filt hF w a)
    (h : ∑ g ∈ G, f g * monoBasis hF g ^ (Fintype.card k ^ m) = 0) :
    ∀ g ∈ G, f g = 0 := by
  classical
  set q₁ := Fintype.card k ^ m with hq₁
  set B := monoBasis hF
  have hF' := baseChange_monic L hF
  have hdeg := natDegree_baseChange L hF
  set B' := monoBasis hF'
  let e : ℕ × Fin F.natDegree → ℕ × Fin (baseChange L F).natDegree :=
    fun l => (l.1, Fin.cast hdeg.symm l.2)
  have he : Function.Injective e := by
    intro l l' hll'
    simp only [e, Prod.mk.injEq] at hll'
    exact Prod.ext hll'.1 (Fin.cast_injective _ hll'.2)
  have hw' := baseChange_hw L hF hw
  have hψinj := injective_of_expansion hF' hw' ψ c hψ
  let Ψ : AdjoinRoot F →ₐ[k] L⟦X⟧ := (ψ.restrictScalars k).comp (ι L F)
  have hΨB : ∀ l, Ψ (B l) = ψ (B' (e l)) := fun l => by
    simp only [Ψ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, B, ι_monoBasis L hF, B', e]
  have hFr : ∀ z : L⟦X⟧, (FiniteField.frobeniusAlgHom k L⟦X⟧ ^ m) z = z ^ q₁ :=
    frobeniusAlgHom_pow_apply m
  have hq₁pos : 0 < q₁ := pow_pos Fintype.card_pos m
  let cf : ℕ × Fin F.natDegree → ℕ × Fin F.natDegree → k := fun g l => B.repr (f g) l
  have hfsum : ∀ g ∈ G, f g = ∑ l ∈ idx F w a, cf g l • B l := by
    intro g hg
    have hsupp : (B.repr (f g)).support ⊆ idx F w a := by
      intro l hl
      exact mem_idx.2 ((mem_filt_iff hF).1 (hf g hg) l (Finsupp.mem_support_iff.1 hl))
    conv_lhs => rw [← B.linearCombination_repr (f g), Finsupp.linearCombination_apply]
    exact Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => zero_smul _ _)
  let v : ℕ × Fin F.natDegree → L⟦X⟧ := fun l => Ψ (B l)
  let P : ℕ × Fin F.natDegree → L⟦X⟧ := fun l => Ψ (∑ g ∈ G, cf g l • B g)
  have hkey : ∑ l ∈ idx F w a, v l * P l ^ q₁ = 0 := by
    have h0 : Ψ (∑ g ∈ G, f g * B g ^ q₁) = 0 := by rw [h, map_zero]
    rw [← h0, map_sum]
    have h1 : ∀ g ∈ G, Ψ (f g * B g ^ q₁) =
        ∑ l ∈ idx F w a, cf g l • (v l * Ψ (B g) ^ q₁) := by
      intro g hg
      rw [map_mul, map_pow, hfsum g hg, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_mul_assoc]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hFr, show P l = Ψ (∑ g ∈ G, cf g l • B g) from rfl, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, map_smul, hFr, mul_smul_comm]
  have hv : ∀ lam : ℕ × Fin F.natDegree → L, (PowerSeries.X : L⟦X⟧) ^ q₁ ∣
      ∑ l ∈ idx F w a, PowerSeries.C (lam l) * v l → ∀ l ∈ idx F w a, lam l = 0 := by
    intro lam hdvd
    set u := ∑ l ∈ idx F w a, lam l • B' (e l)
    have hψu : ψ u = ∑ l ∈ idx F w a, PowerSeries.C (lam l) * v l := by
      simp only [u, map_sum, map_smul, PowerSeries.smul_eq_C_mul, v, hΨB]
    have hu : u ∈ filt hF' w a := by
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (monoBasis_mem_filt hF' ?_)
      simpa [e] using mem_idx.1 hl
    have hu0 : u = 0 := by
      by_contra hu0
      refine not_X_pow_dvd hF' hw' ψ c hψ hu hu0 ?_
      rw [hψu]
      refine dvd_trans (pow_dvd_pow _ ?_) hdvd
      rw [hdeg]; omega
    have hli := linearIndependent_iff'.1 (B'.linearIndependent.comp e he)
    exact hli (idx F w a) lam hu0
  have hP := eq_zero_of_sum_mul_pow_eq_zero hq₁pos
    (fun x y => by rw [← hFr, ← hFr, ← hFr, map_add]) (idx F w a) v P hv hkey
  intro g hg
  have hc : ∀ l ∈ idx F w a, cf g l = 0 := by
    intro l hl
    have h1 : ψ (∑ g ∈ G, algebraMap k L (cf g l) • B' (e g)) = 0 := by
      rw [← hP l hl]
      simp only [P, Ψ, map_sum, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [ι_monoBasis L hF, algebraMap_smul]
    have h2 := hψinj (h1.trans (map_zero ψ).symm)
    have hli := linearIndependent_iff'.1 (B'.linearIndependent.comp e he)
    have := hli G (fun g => algebraMap k L (cf g l)) h2 g hg
    exact (algebraMap k L).injective (this.trans (map_zero _).symm)
  rw [hfsum g hg]
  exact Finset.sum_eq_zero fun l hl => by rw [hc l hl, zero_smul]

end NonCancellation

end RiemannMasullo.WeilBound
