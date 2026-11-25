module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Weil's bound, I: the weighted-degree filtration of a plane curve

Let `K` be a field and `F ∈ K[t][Y]` monic in `Y` of degree `d`, with
`deg_t F_i ≤ (d - i) w` for the coefficients `F_i` of `Y ^ i` (`i < d`). In
`A = K[t][Y] / (F)`, write `t` and `y` for the classes of `t` and `Y`.

The monomials `t ^ j y ^ i` (`i < d`) form a `K`-basis of `A` (`monoBasis`), and
`filt w n` is the span of those of weight `j + w i ≤ n`. This filtration is multiplicative
(`mul_mem_filt`), has dimension `d n + O(1)` (`finrank_filt_le`, `le_finrank_filt`), and
exhausts `A`. It replaces the Riemann–Roch spaces `L(n D)` in Bombieri's proof of Weil's bound:
the only consequence of Riemann–Roch the proof uses is this linear growth.

The zero count (`card_algHom_apply_eq_zero_le`): when `A` is a domain, a nonzero `h` of weight
`≤ n` is killed by at most `d n + w d²` algebra homomorphisms from `A` to a field.
-/

@[expose] public section

open Polynomial

namespace RiemannMasullo.WeilBound

variable {K : Type*} [Field K] {F : K[X][X]} (hF : F.Monic)

/-- The monomial basis `t ^ j * y ^ i` (`i < deg F`) of `K[t][y] / F(t, y)` over `K`. -/
noncomputable def monoBasis : Module.Basis (ℕ × Fin F.natDegree) K (AdjoinRoot F) :=
  (Polynomial.basisMonomials K).smulTower (AdjoinRoot.powerBasis' hF).basis

theorem monoBasis_apply (l : ℕ × Fin F.natDegree) :
    monoBasis hF l = AdjoinRoot.of F (X ^ l.1) * AdjoinRoot.root F ^ (l.2 : ℕ) := by
  unfold monoBasis
  erw [Module.Basis.smulTower_apply]
  rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, coe_basisMonomials]
  dsimp only
  rw [← monomial_one_right_eq_X_pow]
  congr 1
  exact (AdjoinRoot.powerBasis' hF).basis_eq_pow _

/-- The indices of weight at most `n`, the weight of `t ^ j * y ^ i` being `j + w * i`. -/
noncomputable def idx (F : K[X][X]) (w n : ℕ) : Finset (ℕ × Fin F.natDegree) :=
  (Finset.range (n + 1) ×ˢ Finset.univ).filter fun l => l.1 + w * l.2 ≤ n

theorem mem_idx {w n : ℕ} {l : ℕ × Fin F.natDegree} : l ∈ idx F w n ↔ l.1 + w * l.2 ≤ n := by
  simp only [idx, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    and_true, and_iff_right_iff_imp]
  omega

/-- The filtration by weighted degree. -/
noncomputable def filt (w n : ℕ) : Submodule K (AdjoinRoot F) :=
  Submodule.span K (monoBasis hF '' ↑(idx F w n))

theorem mem_filt_iff {w n : ℕ} {x : AdjoinRoot F} :
    x ∈ filt hF w n ↔ ∀ l, (monoBasis hF).repr x l ≠ 0 → l.1 + w * l.2 ≤ n := by
  rw [filt, Module.Basis.mem_span_image]
  constructor
  · intro h l hl
    exact mem_idx.1 (h (Finsupp.mem_support_iff.2 hl))
  · intro h l hl
    exact mem_idx.2 (h l (Finsupp.mem_support_iff.1 hl))

theorem filt_mono (w : ℕ) {m n : ℕ} (h : m ≤ n) : filt hF w m ≤ filt hF w n := by
  intro x hx
  rw [mem_filt_iff] at hx ⊢
  intro l hl
  exact (hx l hl).trans h

theorem monoBasis_mem_filt {w n : ℕ} {l : ℕ × Fin F.natDegree} (h : l.1 + w * l.2 ≤ n) :
    monoBasis hF l ∈ filt hF w n :=
  Submodule.subset_span ⟨l, mem_idx.2 h, rfl⟩

theorem exists_mem_filt (w : ℕ) (x : AdjoinRoot F) : ∃ n, x ∈ filt hF w n := by
  classical
  refine ⟨∑ l ∈ ((monoBasis hF).repr x).support, (l.1 + w * l.2), ?_⟩
  rw [mem_filt_iff]
  intro l hl
  exact Finset.single_le_sum (f := fun l : ℕ × Fin F.natDegree => l.1 + w * l.2)
    (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hl)

theorem finrank_filt (w n : ℕ) : Module.finrank K (filt hF w n) = (idx F w n).card := by
  have h := finrank_span_eq_card (R := K)
    ((monoBasis hF).linearIndependent.comp (Subtype.val : idx F w n → _) Subtype.val_injective)
  rw [Fintype.card_coe] at h
  rw [← h, filt, Set.range_comp, Subtype.range_coe_subtype]
  rfl

theorem card_idx_le (w n : ℕ) : (idx F w n).card ≤ F.natDegree * (n + 1) := by
  calc (idx F w n).card ≤ (Finset.range (n + 1) ×ˢ (Finset.univ : Finset (Fin F.natDegree))).card :=
        Finset.card_filter_le _ _
    _ = _ := by simp [mul_comm]

theorem le_card_idx (w n : ℕ) :
    F.natDegree * (n + 1) ≤ (idx F w n).card + w * F.natDegree * F.natDegree := by
  have hsub : (Finset.range (n + 1 - w * F.natDegree) ×ˢ
      (Finset.univ : Finset (Fin F.natDegree))) ⊆ idx F w n := by
    intro l hl
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at hl
    rw [mem_idx]
    have h1 : (l.2 : ℕ) < F.natDegree := l.2.2
    have h2 : w * (l.2 : ℕ) ≤ w * F.natDegree := Nat.mul_le_mul_left _ h1.le
    omega
  have := Finset.card_le_card hsub
  simp only [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at this
  have h3 : (n + 1) * F.natDegree ≤ (n + 1 - w * F.natDegree) * F.natDegree +
      w * F.natDegree * F.natDegree := by
    rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  nlinarith



theorem finrank_filt_le (w n : ℕ) : Module.finrank K (filt hF w n) ≤ F.natDegree * (n + 1) :=
  (finrank_filt hF w n).trans_le (card_idx_le w n)

theorem le_finrank_filt (w n : ℕ) :
    F.natDegree * (n + 1) ≤ Module.finrank K (filt hF w n) + w * F.natDegree * F.natDegree :=
  (finrank_filt hF w n) ▸ le_card_idx w n

instance (w n : ℕ) : Module.Finite K (filt hF w n) :=
  FiniteDimensional.span_of_finite K ((idx F w n).finite_toSet.image _)

include hF in
/-- The equation of `y = root F` over `K[t]`: `y ^ d = - ∑_{l < d} F_l(t) y ^ l`. -/
theorem root_pow_natDegree :
    AdjoinRoot.root F ^ F.natDegree = -∑ l ∈ Finset.range F.natDegree,
      AdjoinRoot.of F (F.coeff l) * AdjoinRoot.root F ^ l := by
  have h := congrArg (eval₂ (AdjoinRoot.of F) (AdjoinRoot.root F)) hF.as_sum
  rw [AdjoinRoot.eval₂_root, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at h
  replace h := h.symm
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow] at h
  exact eq_neg_of_add_eq_zero_left h

variable {w : ℕ} (hw : ∀ i < F.natDegree, (F.coeff i).natDegree ≤ (F.natDegree - i) * w)
include hw

theorem of_mul_root_pow_mem_filt (i : ℕ) : ∀ (p : K[X]) (n : ℕ), p.natDegree + w * i ≤ n →
    AdjoinRoot.of F p * AdjoinRoot.root F ^ i ∈ filt hF w n := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro p n hn
  by_cases hi : i < F.natDegree
  · have hp := p.as_sum_range_C_mul_X_pow
    rw [hp, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hm' : m ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have : AdjoinRoot.of F (C (p.coeff m) * X ^ m) * AdjoinRoot.root F ^ i =
        p.coeff m • monoBasis hF (m, ⟨i, hi⟩) := by
      rw [monoBasis_apply, Algebra.smul_def, map_mul, mul_assoc]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (monoBasis_mem_filt hF (by simp only; omega))
  · push Not at hi
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi
    have : AdjoinRoot.of F p * AdjoinRoot.root F ^ (F.natDegree + e) =
        -∑ l ∈ Finset.range F.natDegree,
          AdjoinRoot.of F (p * F.coeff l) * AdjoinRoot.root F ^ (e + l) := by
      rw [pow_add, root_pow_natDegree hF, neg_mul, mul_neg, neg_inj, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, pow_add]; ring
    rw [this]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun l hl => ?_)
    have hl' := Finset.mem_range.1 hl
    refine ih (e + l) (by omega) _ _ ?_
    have h1 := natDegree_mul_le (p := p) (q := F.coeff l)
    have h2 := hw l hl'
    have h3 : (F.natDegree - l) * w + w * (e + l) = w * (F.natDegree + e) := by
      rw [mul_comm (F.natDegree - l), ← mul_add]; congr 1; omega
    omega


theorem of_mem_filt (p : K[X]) : AdjoinRoot.of F p ∈ filt hF w p.natDegree := by
  simpa using of_mul_root_pow_mem_filt hF hw 0 p p.natDegree (by simp)

theorem root_pow_mem_filt (i : ℕ) : AdjoinRoot.root F ^ i ∈ filt hF w (w * i) := by
  simpa using of_mul_root_pow_mem_filt hF hw i 1 (w * i) (by simp)

theorem one_mem_filt : (1 : AdjoinRoot F) ∈ filt hF w 0 := by
  simpa using root_pow_mem_filt hF hw 0

theorem mul_mem_filt {a b : AdjoinRoot F} {m n : ℕ} (ha : a ∈ filt hF w m)
    (hb : b ∈ filt hF w n) : a * b ∈ filt hF w (m + n) := by
  have hle : filt hF w m * filt hF w n ≤ filt hF w (m + n) := by
    rw [filt, filt, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨l', hl', rfl⟩, rfl⟩
    rw [Finset.mem_coe, mem_idx] at hl hl'
    have : monoBasis hF l * monoBasis hF l' =
        AdjoinRoot.of F (X ^ (l.1 + l'.1)) * AdjoinRoot.root F ^ ((l.2 : ℕ) + l'.2) := by
      rw [monoBasis_apply, monoBasis_apply, pow_add, pow_add, map_mul]; ring
    simp only [SetLike.mem_coe]
    rw [this]
    exact of_mul_root_pow_mem_filt hF hw _ _ _ (by rw [natDegree_X_pow]; nlinarith)
  exact hle (Submodule.mul_mem_mul ha hb)

theorem pow_mem_filt {a : AdjoinRoot F} {m : ℕ} (ha : a ∈ filt hF w m) (e : ℕ) :
    a ^ e ∈ filt hF w (e * m) := by
  induction e with
  | zero => simpa using one_mem_filt hF hw
  | succ e ih =>
    rw [pow_succ, add_mul, one_mul]
    exact mul_mem_filt hF hw ih ha


/-- The dimension count behind the zero count: if a `K`-linear map `Λ` kills `h A` for a nonzero
`h` of weight `≤ n`, then `Λ` maps each `filt w N` (`N ≥ n`) onto a space of dimension
`≤ d n + w d²`. -/
theorem finrank_map_filt_le [IsDomain (AdjoinRoot F)] {V : Type*} [AddCommGroup V] [Module K V]
    (Λ : AdjoinRoot F →ₗ[K] V) {h : AdjoinRoot F} {n : ℕ} (hh : h ∈ filt hF w n) (h0 : h ≠ 0)
    (hΛ : ∀ x, Λ (h * x) = 0) {N : ℕ} (hN : n ≤ N) :
    Module.finrank K ((filt hF w N).map Λ) ≤ F.natDegree * n + w * F.natDegree * F.natDegree := by
  let π : filt hF w N →ₗ[K] V := Λ ∘ₗ (filt hF w N).subtype
  have hπ : LinearMap.range π = (filt hF w N).map Λ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hπ]
  have h2 := LinearMap.finrank_range_add_finrank_ker π
  let μ : filt hF w (N - n) →ₗ[K] LinearMap.ker π :=
    { toFun := fun x => ⟨⟨h * x, by
          have := mul_mem_filt hF hw hh x.2
          rwa [show n + (N - n) = N by omega] at this⟩, by
          simp [π, hΛ]⟩
      map_add' := fun x y => by ext; simp [mul_add]
      map_smul' := fun c x => by ext; simp }
  have hμ : Function.Injective μ := by
    intro x y hxy
    have := congrArg (fun z : LinearMap.ker π => ((z : filt hF w N) : AdjoinRoot F)) hxy
    simp only [μ, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact Subtype.ext (mul_left_cancel₀ h0 this)
  have h3 := LinearMap.finrank_le_finrank_of_injective hμ
  have h4 := finrank_filt_le hF w N
  have h5 := le_finrank_filt hF w (N - n)
  have h6 : F.natDegree * (N + 1) = F.natDegree * (N - n + 1) + F.natDegree * n := by
    rw [← mul_add]; congr 1; omega
  omega

/-- The zero count behind Bombieri's method: a nonzero `h` of weighted degree `≤ n` has
`dim_K A / h A ≤ d n + w d²`. -/
theorem rank_quotient_le [IsDomain (AdjoinRoot F)] {h : AdjoinRoot F} {n : ℕ}
    (hh : h ∈ filt hF w n) (h0 : h ≠ 0) :
    Module.rank K (AdjoinRoot F ⧸ Ideal.span {h}) ≤
      (F.natDegree * n + w * F.natDegree * F.natDegree : ℕ) := by
  classical
  set I := Ideal.span {h}
  apply _root_.rank_le
  intro s hs
  have hlift : ∀ x : AdjoinRoot F ⧸ I, ∃ a : AdjoinRoot F, Ideal.Quotient.mk I a = x :=
    fun x => Ideal.Quotient.mk_surjective x
  choose lift hlift using hlift
  have hN : ∀ x, ∃ m, lift x ∈ filt hF w m := fun x => exists_mem_filt hF w (lift x)
  choose deg hdeg using hN
  set N := n + ∑ x ∈ s, deg x
  have hmem : ∀ x ∈ s, lift x ∈ filt hF w N := fun x hx =>
    filt_mono hF w (by
      have := Finset.single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hx
      omega) (hdeg x)
  let Λ : AdjoinRoot F →ₗ[K] AdjoinRoot F ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  have hspan : Submodule.span K (s : Set (AdjoinRoot F ⧸ I)) ≤ (filt hF w N).map Λ := by
    rw [Submodule.span_le]
    intro x hx
    exact ⟨lift x, hmem x hx, hlift x⟩
  have h1 : s.card ≤ Module.finrank K ((filt hF w N).map Λ) := by
    rw [← finrank_span_finset_eq_card hs]
    exact Submodule.finrank_mono hspan
  have := finrank_map_filt_le hF hw Λ hh h0 (fun x => by
    simp [Λ, I]) (N := N) (by omega)
  exact_mod_cast h1.trans this

/-- At most `d n + w d²` algebra homomorphisms to a field kill a nonzero `h` of weighted degree
`≤ n`. -/
theorem card_algHom_apply_eq_zero_le [IsDomain (AdjoinRoot F)] (L : Type*) [Field L]
    [Algebra K L] {h : AdjoinRoot F} {n : ℕ} (hh : h ∈ filt hF w n) (h0 : h ≠ 0) :
    Finite {φ : AdjoinRoot F →ₐ[K] L // φ h = 0} ∧
      Nat.card {φ : AdjoinRoot F →ₐ[K] L // φ h = 0} ≤
        F.natDegree * n + w * F.natDegree * F.natDegree := by
  have hr := rank_quotient_le hF hw hh h0
  have hfin : Module.Finite K (AdjoinRoot F ⧸ Ideal.span {h}) :=
    Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.natCast_lt_aleph0))
  let e : {φ : AdjoinRoot F →ₐ[K] L // φ h = 0} ≃ (AdjoinRoot F ⧸ Ideal.span {h} →ₐ[K] L) :=
    { toFun := fun φ => Ideal.Quotient.liftₐ _ φ.1 (fun a ha => by
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
          simp [φ.2])
      invFun := fun ψ => ⟨ψ.comp (Ideal.Quotient.mkₐ K _), by
          simp [Ideal.Quotient.mkₐ_eq_mk]⟩
      left_inv := fun φ => Subtype.ext (AlgHom.ext fun a => rfl)
      right_inv := fun ψ => by
        ext x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e]
  exact (card_algHom_le_finrank K _ L).trans (Module.finrank_le_of_rank_le hr)

end RiemannMasullo.WeilBound
