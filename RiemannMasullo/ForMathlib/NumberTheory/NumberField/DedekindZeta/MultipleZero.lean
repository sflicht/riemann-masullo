module

public import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.VerticalStrip
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int

/-! # A multiple zero of a completed Dedekind zeta function

For the splitting field of X³ − 2, the Euler factors give an identity of zeta
orders with the cubic and quadratic subfields. The cubic zeta function has
larger zero order than the rational zeta function somewhere in the open strip.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set Filter Function Topology
open scoped NNReal ENNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "order(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat

/-- Grouping prime ideals by their norm raises each Euler factor to the number
of prime ideals of that norm. -/
private theorem spectralLineJet_memLp_false_groupedEuler (E : Type) [Field E] [NumberField E]
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun n : ℕ ↦ ((1 - (n : ℂ) ^ (-s))⁻¹) ^
      Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = n})
      (dedekindZeta E s) := by
  classical
  let u (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) := v.asIdeal.absNorm
  let e := Equiv.sigmaFiberEquiv u
  apply (e.hasProd_iff.mpr (dedekindZeta_hasProd E hs)).sigma
  intro n
  have : Finite {I : Ideal (𝓞 E) // I.absNorm = n} :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).to_subtype
  let g (v : {v // u v = n}) : {I : Ideal (𝓞 E) // I.absNorm = n} := ⟨v.val.asIdeal, v.property⟩
  have : Finite {v // u v = n} := Finite.of_injective g (fun x y hxy ↦ Subtype.ext <|
    IsDedekindDomain.HeightOneSpectrum.ext <| congrArg Subtype.val hxy)
  let := Fintype.ofFinite {v // u v = n}
  convert hasProd_fintype (fun _ : {v // u v = n} ↦ (1 - (n : ℂ) ^ (-s))⁻¹) using 1
  · ext v
    change (1 - (u v.val : ℂ) ^ (-s))⁻¹ = _
    rw [v.property]
  · rw [Finset.prod_const, Finset.card_univ]
    exact congrArg _ (Nat.card_eq_fintype_card (α := {v // u v = n}))

/-- A local Euler denominator is nonzero whenever its argument has positive real part. -/
private theorem spectralLineJet_memLp_false_denominator (n : ℕ) (hn : 1 < n) (s : ℂ) (hs : 0 < s.re) :
    1 - (n : ℂ) ^ (-s) ≠ 0 := by
  have hlt : ‖(n : ℂ) ^ (-s)‖ < 1 := by
    change ‖((n : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (n : ℝ)), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (neg_lt_zero.mpr hs)
  intro he
  rw [(sub_eq_zero.mp he).symm, norm_one] at hlt
  exact hlt.false

/-- A finite product of reciprocal Euler denominators is entire and nonvanishing in Re(s) > 0. -/
private theorem spectralLineJet_memLp_false_finiteFactor (A : Finset ℕ) (hA : ∀ n ∈ A, 1 < n) (a : ℕ → ℕ) :
    let C : ℂ → ℂ := fun s ↦ ∏ n ∈ A, (1 - (n : ℂ) ^ (-s)) ^ a n
    AnalyticOnNhd ℂ C univ ∧ ∀ s : ℂ, 0 < s.re → C s ≠ 0 := by
  intro C
  constructor
  · intro s _
    apply Differentiable.analyticAt
    dsimp [C]
    apply Differentiable.fun_finsetProd
    intro n hn
    have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hA n hn; omega)
    exact ((differentiable_const (1 : ℂ)).sub (differentiable_id.neg.const_cpow (Or.inl this))).pow _
  · intro s hs
    exact Finset.prod_ne_zero_iff.mpr fun n hn ↦
      pow_ne_zero _ (spectralLineJet_memLp_false_denominator n (hA n hn) s hs)

/-- Cancel the exceptional Euler factors in two products that agree outside a finite set. -/
private theorem spectralLineJet_memLp_false_discardFinite (A : Finset ℕ) (hA : ∀ n ∈ A, 1 < n) (a b : ℕ → ℕ)
    (h : ∀ n ∉ A, a n = b n) (s : ℂ) (hs : 0 < s.re) (x y : ℂ)
    (hx : HasProd (fun n : ℕ ↦ ((1 - (n : ℂ) ^ (-s))⁻¹) ^ a n) x)
    (hy : HasProd (fun n : ℕ ↦ ((1 - (n : ℂ) ^ (-s))⁻¹) ^ b n) y) :
    x * (∏ n ∈ A, (1 - (n : ℂ) ^ (-s)) ^ a n) =
      y * (∏ n ∈ A, (1 - (n : ℂ) ^ (-s)) ^ b n) := by
  classical
  let z (n : ℕ) := 1 - (n : ℂ)^(-s)
  have hc (k : ℕ → ℕ) : HasProd (fun n ↦ if n ∈ A then z n ^ k n else 1)
      (∏ n ∈ A, z n ^ k n) := by
    have H : HasProd (fun n ↦ if n ∈ A then z n ^ k n else 1)
        (∏ n ∈ A, if n ∈ A then z n ^ k n else 1) :=
      hasProd_prod_of_ne_finset_one (s := A) (fun n hn ↦ by simp [hn])
    simpa using H
  refine ((hx.mul (hc a)).congr_fun (fun n ↦ ?_)).unique (hy.mul (hc b))
  change (z n)⁻¹ ^ b n * _ = (z n)⁻¹ ^ a n * _
  by_cases hn : n ∈ A
  · have hnz : z n ≠ 0 := spectralLineJet_memLp_false_denominator n (hA n hn) s hs
    simp [hn, inv_pow, hnz]
  · rw [h n hn]

/-- After omitting finitely many prime norms, the Euler identity has only
finite Euler factors as corrections. Those factors are entire and are
nonzero on the open right half-plane. -/
private theorem spectralLineJet_memLp_false_zetaRelation
    (L k K : Type) [Field L] [NumberField L] [Field k] [NumberField k] [Field K] [NumberField K]
    (h : let count := fun (E : Type) [Field E] [NumberField E] (n : ℕ) ↦
       Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = n}
       ∃ A : Finset ℕ, (∀ n ∈ A, 1 < n) ∧
         ∀ n ∉ A, count L n + 2 * count ℚ n = count k n + 2 * count K n) :
    ∃ P Q : ℂ → ℂ, AnalyticOnNhd ℂ P univ ∧ AnalyticOnNhd ℂ Q univ ∧
      (∀ s : ℂ, 0 < s.re → P s ≠ 0 ∧ Q s ≠ 0) ∧ ∀ s : ℂ, 1 < s.re →
      (dedekindZeta L s * dedekindZeta ℚ s ^ 2) * P s =
        (dedekindZeta k s * dedekindZeta K s ^ 2) * Q s := by
  let count := fun (E : Type) [Field E] [NumberField E] (n : ℕ) ↦
    Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = n}
  let a := fun n ↦ count L n + 2 * count ℚ n
  let b := fun n ↦ count k n + 2 * count K n
  obtain ⟨A, hA, hcount⟩ := h
  have hP := spectralLineJet_memLp_false_finiteFactor A hA a
  have hQ := spectralLineJet_memLp_false_finiteFactor A hA b
  refine ⟨_, _, hP.1, hQ.1, fun s hs ↦ ⟨hP.2 s hs, hQ.2 s hs⟩, fun s hs ↦ ?_⟩
  apply spectralLineJet_memLp_false_discardFinite A hA a b hcount s (by linarith)
  · have hL := (spectralLineJet_memLp_false_groupedEuler L s hs).mul
      ((spectralLineJet_memLp_false_groupedEuler ℚ s hs).pow 2)
    exact hL.congr_fun fun n ↦ by simp only [a, count, pow_add, mul_comm 2, pow_mul]
  · have hk := (spectralLineJet_memLp_false_groupedEuler k s hs).mul
      ((spectralLineJet_memLp_false_groupedEuler K s hs).pow 2)
    exact hk.congr_fun fun n ↦ by simp only [b, count, pow_add, mul_comm 2, pow_mul]

/-- In the open strip a Dedekind zeta order is finite and nonnegative. -/
private theorem spectralLineJet_memLp_false_stripOrder (E : Type) [Field E] [NumberField E]
    (s : ℂ) (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(E))) s =
      (order((1 : PontryaginDual C𝔽(E)), s) : WithTop ℤ) := by
  let χ : PontryaginDual C𝔽(E) := 1
  let Λ := continuedCompletedHeckeL χ
  have hΛ := continuedCompletedHeckeL_spec χ
  obtain ⟨t, ⟨-, -, hp, ha⟩, -⟩ := completedHeckeL_continuation_simplePoles χ Λ hΛ.1 hΛ.2 (by rfl)
  have hn := hΛ.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ s) (by rw [hp]; simp)
  have hpos := (ha s (by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> intro he <;> have := congrArg Complex.re he <;>
      simp [Complex.add_re, Complex.mul_re] at this <;> linarith)).meromorphicOrderAt_nonneg
  change meromorphicOrderAt Λ s = ((meromorphicOrderAt Λ s).untop₀.toNat : WithTop ℤ)
  rw [← WithTop.coe_untop₀_of_ne_top hn] at hpos ⊢
  simp only [WithTop.untop₀_coe, ← WithTop.coe_zero, WithTop.coe_le_coe] at hpos ⊢
  exact_mod_cast (Int.toNat_of_nonneg hpos).symm

/-- Continue the zeta identity from its Euler products and take divisors in the open strip. -/
private theorem spectralLineJet_memLp_false_orderRelation
    (L k K : Type) [Field L] [NumberField L] [Field k] [NumberField k] [Field K] [NumberField K]
    (h : ∃ P Q : ℂ → ℂ, AnalyticOnNhd ℂ P univ ∧ AnalyticOnNhd ℂ Q univ ∧
      (∀ s : ℂ, 0 < s.re → P s ≠ 0 ∧ Q s ≠ 0) ∧ ∀ s : ℂ, 1 < s.re →
      (dedekindZeta L s * dedekindZeta ℚ s ^ 2) * P s =
        (dedekindZeta k s * dedekindZeta K s ^ 2) * Q s)
    (z : ℂ) (h₀ : 0 < z.re) (h₁ : z.re < 1) :
    order((1 : PontryaginDual C𝔽(L)), z) + 2 * order((1 : PontryaginDual C𝔽(ℚ)), z) =
      order((1 : PontryaginDual C𝔽(k)), z) + 2 * order((1 : PontryaginDual C𝔽(K)), z) := by
  let f (E : Type) [Field E] [NumberField E] :=
    (finiteHeckeL_exists_continuation (1 : PontryaginDual C𝔽(E))).choose
  have hf (E : Type) [Field E] [NumberField E] := (finiteHeckeL_exists_continuation
    (1 : PontryaginDual C𝔽(E))).choose_spec
  have hm (E : Type) [Field E] [NumberField E] : MeromorphicOn (f E) univ :=
    (hf E).1.meromorphicOn
  have hζ (E : Type) [Field E] [NumberField E] (s : ℂ) (hs : 1 < s.re) :
      f E s = dedekindZeta E s := ((hf E).2 ⟨s, hs⟩).trans (finiteHeckeL_one_eq_dedekindZeta _)
  have ho (E : Type) [Field E] [NumberField E] :
      meromorphicOrderAt (f E) z = (order((1 : PontryaginDual C𝔽(E)), z) : WithTop ℤ) :=
    (meromorphicOrderAt_finiteHeckeL_continuation _ (hm E) (hf E).2 h₀).trans
      (spectralLineJet_memLp_false_stripOrder E z h₀ h₁)
  obtain ⟨P, Q, hP, hQ, hPQ, heq⟩ := h
  have hP₀ := (hP z (mem_univ _)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hPQ z h₀).1
  have hQ₀ := (hQ z (mem_univ _)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hPQ z h₀).2
  have he := meromorphicContinuation_eventuallyEq (((hm L).mul ((hm ℚ).pow 2)).mul hP.meromorphicOn)
    (((hm k).mul ((hm K).pow 2)).mul hQ.meromorphicOn) (fun s hs ↦ by
      change (f L s * f ℚ s ^ 2) * P s = (f k s * f K s ^ 2) * Q s
      simpa only [hζ _ s hs] using heq s hs) z
  have hd := meromorphicOrderAt_congr he
  have hproj (E T : Type) [Field E] [NumberField E] [Field T] [NumberField T] (U : ℂ → ℂ)
      (hU : AnalyticAt ℂ U z) (hord : meromorphicOrderAt U z = 0) :
      meromorphicOrderAt ((f E * f T ^ 2) * U) z = meromorphicOrderAt (f E) z +
        (2 : ℕ) * meromorphicOrderAt (f T) z := by
    rw [meromorphicOrderAt_mul (((hm E z (mem_univ _)).mul ((hm T z (mem_univ _)).pow 2)))
        hU.meromorphicAt, hord, add_zero,
      meromorphicOrderAt_mul ((hm E) z (mem_univ _)) ((hm T z (mem_univ _)).pow 2),
      meromorphicOrderAt_pow (hm T z (mem_univ _))]
  rw [hproj L ℚ P (hP z (mem_univ _)) hP₀, hproj k K Q (hQ z (mem_univ _)) hQ₀,
    ho, ho, ho, ho] at hd
  have hnat (a b c d : ℕ) (h : (a : WithTop ℤ) + (2 : ℕ) * (b : WithTop ℤ) =
      (c : WithTop ℤ) + (2 : ℕ) * (d : WithTop ℤ)) : a + 2 * b = c + 2 * d := by
    have hi := congrArg WithTop.untop₀ h
    change (a : ℤ) + 2 * b = c + 2 * d at hi
    omega
  exact hnat _ _ _ _ hd

/-- The action on the three complex roots of X³ − 2 is the full symmetric group.
Complex conjugation exchanges the two nonreal roots, and the irreducible cubic
has prime degree. -/
private theorem spectralLineJet_memLp_false_cubicGalois (P : Polynomial ℚ)
    (hp : P = Polynomial.X ^ 3 - Polynomial.C 2) (hirr : Irreducible P) :
    Nonempty ((P.SplittingField ≃ₐ[ℚ] P.SplittingField) ≃* Equiv.Perm (Fin 3)) := by
  classical
  have hd : P.natDegree = 3 := hp ▸ Polynomial.natDegree_X_pow_sub_C (2 : ℚ)
  have hc := (Polynomial.card_rootSet_eq_natDegree hirr.separable
    (IsAlgClosed.splits _ : (P.map (algebraMap ℚ ℂ)).Splits)).trans hd
  have hpow (x : P.rootSet ℝ) : x.val ^ 3 = 2 := by
    have hx := (Polynomial.mem_rootSet_of_ne hirr.ne_zero).mp x.property
    simpa [hp, sub_eq_zero] using hx
  have : Subsingleton (P.rootSet ℝ) := ⟨fun x y ↦ Subtype.ext <|
    (show Odd 3 by decide).pow_injective ((hpow x).trans (hpow y).symm)⟩
  have hreal : Fintype.card (P.rootSet ℝ) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hh := Polynomial.Gal.galActionHom_bijective_of_prime_degree' hirr (by rw [hd]; decide)
    (by omega) (by omega)
  exact ⟨(MulEquiv.ofBijective _ hh).trans (Fintype.equivFinOfCardEq hc).permCongrHom⟩

/-- Invert the sums of the counts of cycles with lengths dividing r, weighting
each cycle by its length. -/
private theorem spectralLineJet_memLp_false_invertTraces (a b : ℕ → ℕ)
    (h : ∀ r : ℕ, 0 < r → ∑ d ∈ r.divisors, d * a d = ∑ d ∈ r.divisors, d * b d) :
    ∀ r, 0 < r → a r = b r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hmem := Nat.mem_divisors.mpr (And.intro (dvd_refl r) hr.ne')
    have hproper : ∑ d ∈ r.divisors.erase r, d * a d = ∑ d ∈ r.divisors.erase r, d * b d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdm := Finset.mem_erase.mp hd
      have hdiv := (Nat.mem_divisors.mp hdm.2).1
      rw [ih d (lt_of_le_of_ne (Nat.le_of_dvd hr hdiv) hdm.1) (Nat.pos_of_dvd_of_pos hdiv hr)]
    have ht := h r hr
    rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem, hproper] at ht
    exact Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel ht)

open Finset in
/-- The transitive actions of S₃ on two and three points have the sign and
standard permutation characters, respectively. Enumerate the six words in
the two adjacent transpositions and their possible images. -/
private theorem spectralLineJet_memLp_false_transitiveCharacters
    (φ : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 2))
    (ψ : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3))
    (hφ : ∀ i j, ∃ g, φ g i = j) (hψ : ∀ i j, ∃ g, ψ g i = j)
    (σ : Equiv.Perm (Fin 3)) :
    (univ.filter fun i : Fin 2 ↦ φ σ i = i).card = (if Equiv.Perm.sign σ = 1 then 2 else 0) ∧
      (univ.filter fun i : Fin 3 ↦ ψ σ i = i).card = (univ.filter fun i : Fin 3 ↦ σ i = i).card := by
  let word {G : Type} [Monoid G] (x y : G) (n : Fin 6) : G := ![1, x, y, x * y, y * x, x * y * x] n
  let s := Equiv.swap (0 : Fin 3) 1
  let t := Equiv.swap (1 : Fin 3) 2
  have hall (σ : Equiv.Perm (Fin 3)) : ∃ n : Fin 6, word s t n = σ := by
    decide +revert
  have hrel {G : Type} [Monoid G] (f : Equiv.Perm (Fin 3) →* G) :
      (f s) ^ 2 = 1 ∧ (f t) ^ 2 = 1 ∧ (f s * f t) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_pow,
      show s ^ 2 = 1 by decide, show t ^ 2 = 1 by decide, show (s * t) ^ 3 = 1 by decide, map_one]
    simp
  have hword {G : Type} [Monoid G] (f : Equiv.Perm (Fin 3) →* G) (n : Fin 6) :
      f (word s t n) = word (f s) (f t) n := by fin_cases n <;> simp [word, map_mul]
  have hpre {n : ℕ} (f : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin n))
      (h : ∀ i j, ∃ g, f g i = j) (i j : Fin n) :
      ∃ k : Fin 6, word (f s) (f t) k i = j := by
    obtain ⟨g, hg⟩ := h i j
    obtain ⟨k, rfl⟩ := hall g
    exact ⟨k, (congrArg (fun g : Equiv.Perm (Fin n) ↦ g i) (hword f k).symm).trans hg⟩
  have htwo (x y : Equiv.Perm (Fin 2))
      (_ : x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 3 = 1)
      (_ : ∀ i j, ∃ k : Fin 6, word x y k i = j) (k : Fin 6) :
      (univ.filter fun i : Fin 2 ↦ word x y k i = i).card =
        if Equiv.Perm.sign (word s t k) = 1 then 2 else 0 := by
    clear hpre hword hrel hall hφ hψ φ ψ σ
    decide +revert
  have hthree (x y : Equiv.Perm (Fin 3))
      (_ : x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 3 = 1)
      (_ : ∀ i j, ∃ k : Fin 6, word x y k i = j) (k : Fin 6) :
      (univ.filter fun i : Fin 3 ↦ word x y k i = i).card =
        (univ.filter fun i : Fin 3 ↦ word s t k i = i).card := by
    clear htwo hpre hword hrel hall hφ hψ φ ψ σ
    decide +revert
  obtain ⟨k, rfl⟩ := hall σ
  rw [hword φ, hword ψ]
  exact ⟨htwo _ _ (hrel φ) (hpre φ hφ) k, hthree _ _ (hrel ψ) (hpre ψ hψ) k⟩

/-- The regular and the two transitive S₃ permutation characters satisfy the
Artin relation for every power of Frobenius. -/
private theorem spectralLineJet_memLp_false_character (σ : Equiv.Perm (Fin 3)) :
    (Finset.univ.filter fun g : Equiv.Perm (Fin 3) ↦ σ * g = g).card + 2 =
      (if Equiv.Perm.sign σ = 1 then 2 else 0) +
        2 * (Finset.univ.filter fun i : Fin 3 ↦ σ i = i).card := by
  decide +revert

/-- Every prime-ideal norm is a positive power of a rational prime. -/
private theorem spectralLineJet_memLp_false_countSupport (E : Type) [Field E] [NumberField E] (n : ℕ)
    (hn : ¬ IsPrimePow n) :
    Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = n} = 0 := by
  classical
  by_contra! hp
  obtain ⟨⟨v, hv⟩⟩ := (Nat.card_pos_iff.mp (Nat.zero_lt_of_ne_zero hp)).1
  apply hn
  rw [← hv, Ideal.absNorm_apply]
  let k := (𝓞 E) ⧸ v.asIdeal
  let : Field k := Ideal.Quotient.field v.asIdeal
  let : Fintype k := Fintype.ofFinite k
  change IsPrimePow (Nat.card k)
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card k

/-- A rational prime ideal has norm equal to its natural prime generator. -/
private theorem spectralLineJet_memLp_false_ratNorm (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal.absNorm = (Rat.HeightOneSpectrum.primesEquiv v).val := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hmap : v.asIdeal.map e = (Ideal.span {(p : 𝓞 ℚ)}).map e := by
    simpa [Ideal.map_span, e, p] using (Rat.HeightOneSpectrum.span_natGenerator v).symm
  have he := congrArg (Ideal.comap e) hmap
  simp only [Ideal.comap_map_of_bijective e e.bijective] at he
  rw [he, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  rfl

/-- In ℚ there is one prime ideal of each rational prime norm and none of any other norm. -/
private theorem spectralLineJet_memLp_false_ratCount (n : ℕ) :
    Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) // v.asIdeal.absNorm = n} =
      if n.Prime then 1 else 0 := by
  classical
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  by_cases hp : n.Prime
  · let u := e.symm ⟨n, hp⟩
    have hu : u.asIdeal.absNorm = n := (spectralLineJet_memLp_false_ratNorm u).trans
      (congrArg Subtype.val (e.apply_symm_apply _))
    let : Unique {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) // v.asIdeal.absNorm = n} :=
      { default := ⟨u, hu⟩
        uniq v := Subtype.ext <| e.injective <| Subtype.ext <|
          ((spectralLineJet_memLp_false_ratNorm v.val).symm.trans v.property).trans
            (hu.symm.trans (spectralLineJet_memLp_false_ratNorm u)) }
    simp [hp]
  · have : IsEmpty {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) // v.asIdeal.absNorm = n} :=
      ⟨fun v ↦ hp (((spectralLineJet_memLp_false_ratNorm v.val).symm.trans v.property) ▸ (e v.val).property)⟩
    simp [hp]

/-- Every positive Frobenius power has trace one for the rational zeta factor. -/
private theorem spectralLineJet_memLp_false_ratTrace (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    ∑ d ∈ r.divisors, d *
      Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) // v.asIdeal.absNorm = p ^ d} = 1 := by
  simp_rw [spectralLineJet_memLp_false_ratCount]
  rw [Finset.sum_eq_single (1 : ℕ)]
  · simp [hp]
  · intro d _ hd
    have hh : ¬(p ^ d).Prime := fun h ↦ hd ((h.pow_eq_iff.mp rfl).2)
    simp [hh]
  · simp [Nat.one_mem_divisors.mpr hr.ne']

open Polynomial in
/-- The splitting field of the pure cubic contains a square root of −3.
For distinct cube roots x and y, take (2x+y)/y. -/
private theorem spectralLineJet_memLp_false_resolventSplits (P : Polynomial ℚ)
    (hP : P = X ^ 3 - C 2) (hirr : Irreducible P) :
    ((X ^ 2 + C 3 : Polynomial ℚ).map (algebraMap ℚ P.SplittingField)).Splits := by
  let L := P.SplittingField
  have hsplit := Polynomial.SplittingField.splits P
  have hc := Polynomial.card_rootSet_eq_natDegree hirr.separable hsplit
  have hthree : P.natDegree = 3 := hP ▸ Polynomial.natDegree_X_pow_sub_C (2 : ℚ)
  have hcard : Fintype.card (P.rootSet L) = 3 := hc.trans hthree
  have : Nontrivial (P.rootSet L) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (P.rootSet L)
  have hp (x : P.rootSet L) : x.val ^ 3 = 2 := by
    have hx := (Polynomial.mem_rootSet_of_ne hirr.ne_zero).mp x.property
    simpa [hP, sub_eq_zero] using hx
  have hxny : x.val - y.val ≠ 0 := sub_ne_zero_of_ne (fun e ↦ hxy (Subtype.ext e))
  have hf : (x.val - y.val) * (x.val ^ 2 + x.val * y.val + y.val ^ 2) = 0 := by
    linear_combination (hp x) - (hp y)
  have hq := (mul_eq_zero.mp hf).resolve_left hxny
  have hy : y.val ≠ 0 := fun e ↦ by simpa [e] using hp y
  let a := (2 * x.val + y.val) / y.val
  have hs : a ^ 2 = -3 := by
    dsimp [a]
    field_simp
    linear_combination 4 * hq
  have hpoly : (X ^ 2 + C 3 : Polynomial L) = (X - C a) * (X - C (-a)) := by
    rw [map_neg, sub_neg_eq_add, mul_comm (X - C a), ← sq_sub_sq, ← map_pow, hs, map_neg, sub_neg_eq_add]
  simp [hpoly]


open Polynomial in
/-- The pure cubic and its quadratic resolvent embed into the splitting field.
The resolvent has degree two, as its two conjugate roots are nonreal. -/
private theorem spectralLineJet_memLp_false_subfields (P : Polynomial ℚ) (hP : P = X ^ 3 - C 2)
    (hirr : Irreducible P) :
    let Q : Polynomial ℚ := X ^ 2 + C 3
    Nonempty (AdjoinRoot P →ₐ[ℚ] P.SplittingField) ∧
      Nonempty (Q.SplittingField →ₐ[ℚ] P.SplittingField) ∧
      Module.finrank ℚ Q.SplittingField = 2 := by
  intro Q
  have hdeg : P.degree ≠ 0 := by
    rw [hP, Polynomial.degree_X_pow_sub_C (by decide : 0 < 3)]
    decide
  let b := rootOfSplits (SplittingField.splits P) (by rwa [degree_map])
  have hb : eval₂ (algebraMap ℚ P.SplittingField) b P = 0 := by
    rw [← eval_map]
    exact eval_rootOfSplits ..
  refine ⟨⟨AdjoinRoot.liftAlgHom P (Algebra.ofId ℚ P.SplittingField) b hb⟩,
    ⟨Polynomial.SplittingField.lift Q (spectralLineJet_memLp_false_resolventSplits P hP hirr)⟩, ?_⟩
  have hirrQ : Irreducible Q := by
    have hh := irreducible_X_pow_sub_C_of_prime (by decide : Nat.Prime 2)
      (a := (-3 : ℚ)) (fun x hx ↦ by nlinarith [sq_nonneg x])
    simpa [Q] using hh
  have hd : Q.natDegree = 2 := by dsimp [Q]; compute_degree!
  have hc := (Polynomial.card_rootSet_eq_natDegree hirrQ.separable
    (IsAlgClosed.splits _ : (Q.map (algebraMap ℚ ℂ)).Splits)).trans hd
  have : IsEmpty (Q.rootSet ℝ) := ⟨fun x ↦ by
    have hx := (Polynomial.mem_rootSet_of_ne hirrQ.ne_zero).mp x.property
    have hh : x.val ^ 2 + 3 = 0 := by simpa [Q] using hx
    nlinarith [sq_nonneg x.val]⟩
  have hr : Fintype.card (Q.rootSet ℝ) = 0 := Fintype.card_eq_zero
  have hh := Polynomial.Gal.galActionHom_bijective_of_prime_degree' hirrQ (by rw [hd]; decide)
    (by omega) (by omega)
  rw [← Polynomial.Gal.card_of_separable hirrQ.separable,
    Nat.card_congr (Equiv.ofBijective _ hh), Nat.card_eq_fintype_card, Fintype.card_perm, hc]
  decide

/-- The Galois group acts transitively by postcomposition on the embeddings of
a subfield. Number the embeddings using their equality in number with the degree. -/
private theorem spectralLineJet_memLp_false_embeddingAction
    (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E]
    [IsGalois ℚ L] (ι : E →ₐ[ℚ] L) (n : ℕ) (hn : Module.finrank ℚ E = n) :
    ∃ (e : (E →ₐ[ℚ] L) ≃ Fin n) (ρ : (L ≃ₐ[ℚ] L) →* Equiv.Perm (Fin n)),
      (∀ g i, ρ g (e i) = e (g.toAlgHom.comp i)) ∧ ∀ i j, ∃ g, ρ g i = j := by
  classical
  have hc := AlgHom.card_of_splits ℚ E L (fun x ↦ by
    rw [← minpoly.algHom_eq ι ι.injective]
    exact (inferInstance : Normal ℚ L).splits (ι x))
  let e := Fintype.equivFinOfCardEq (hc.trans hn)
  let post : (L ≃ₐ[ℚ] L) →* Equiv.Perm (E →ₐ[ℚ] L) :=
    { toFun := fun g ↦ AlgEquiv.arrowCongr (AlgEquiv.refl : E ≃ₐ[ℚ] E) g
      map_one' := by ext i x; rfl
      map_mul' := by intro g h; ext i x; rfl }
  let ρ := e.permCongrHom.toMonoidHom.comp post
  have hρ (g : L ≃ₐ[ℚ] L) (i : E →ₐ[ℚ] L) : ρ g (e i) = e (g.toAlgHom.comp i) := by
    change e (post g (e.symm (e i))) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨e, ρ, hρ, ?_⟩
  rintro i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  let := a.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x ↦ (a.commutes x).symm
  let g := AlgEquiv.ofBijective (b.liftNormal L) (AlgHom.normal_bijective ℚ L L _)
  refine ⟨g, (hρ g a).trans (congrArg e ?_)⟩
  ext x
  exact b.liftNormal_commutes L x


/-- Relabeling a finite action preserves the number of fixed points. -/
private theorem spectralLineJet_memLp_false_fixedCount {X Y : Type} [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (s : X → X) (g : Y → Y) (h : ∀ x, g (e x) = e (s x)) :
    Nat.card {x // s x = x} = (Finset.univ.filter fun i ↦ g i = i).card := by
  classical
  let f : {x // s x = x} ≃ {i // g i = i} := e.subtypeEquiv fun x ↦ by rw [h, e.apply_eq_iff_eq]
  rw [Nat.card_congr f, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

/-- Any rational prime has a prime above it in the splitting field and an
arithmetic Frobenius inducing the residue-field power map. -/
private theorem spectralLineJet_memLp_false_frobeniusLift (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (p : ℕ) (hp : p.Prime) :
    ∃ (P : Ideal (𝓞 L)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : L ≃ₐ[ℚ] L), IsArithFrobAt ℤ σ P := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have : q.IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨⟨P, hP, hq⟩⟩ := q.nonempty_primesOver (S := 𝓞 L)
  have : P.IsPrime := hP
  have : P.LiesOver q := hq
  have hq₀ : q ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp (by exact_mod_cast hp.ne_zero)
  have h₀ : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq₀ P
  have := Ring.HasFiniteQuotients.finiteQuotient h₀
  have := IsGaloisGroup.of_isFractionRing (L ≃ₐ[ℚ] L) ℤ (𝓞 L) ℚ L
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (R := ℤ) (G := L ≃ₐ[ℚ] L) (Q := P)
  exact ⟨P, hP, hq, σ, hσ⟩

section

open scoped nonZeroDivisors TensorProduct

/-- A rational prime below an ideal divides the norm of every integer in that ideal. -/
private theorem spectralLineJet_memLp_false_residueNorm (L : Type) [Field L] [NumberField L]
    (p : ℕ) (_hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (x : 𝓞 L) (hx : x ∈ P) : p ∣ (Algebra.norm ℤ x).natAbs := by
  have h := Ideal.natAbs_pow_inertiaDeg (p : ℤ) P
  have h₀ : p ∣ P.absNorm := by
    rw [← h, Int.natAbs_natCast]
    exact dvd_pow_self _ (P.inertiaDeg_pos ℤ).ne'
  exact h₀.trans (by exact_mod_cast (Int.dvd_natAbs.mpr (Ideal.absNorm_dvd_norm_of_mem hx)))

/-- Two distinct embeddings remain distinct modulo every prime outside a finite set. -/
private theorem spectralLineJet_memLp_false_reductionInjective (L E : Type) [Field L] [NumberField L]
    [Field E] [NumberField E] :
    ∀ᶠ p : ℕ in cofinite, p.Prime → ∀ (P : Ideal (𝓞 L)) (_ : P.IsPrime)
      (_ : P.LiesOver (Ideal.span {(p : ℤ)})),
      Function.Injective (fun i : E →ₐ[ℚ] L ↦ (Ideal.Quotient.mk P).comp
        (RingOfIntegers.mapRingHom i.toRingHom)) := by
  classical
  let res (i : E →ₐ[ℚ] L) := RingOfIntegers.mapRingHom i.toRingHom
  have pair (i j : E →ₐ[ℚ] L) : ∀ᶠ p : ℕ in cofinite, p.Prime →
      ∀ (P : Ideal (𝓞 L)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)})),
      (Ideal.Quotient.mk P).comp (res i) = (Ideal.Quotient.mk P).comp (res j) → i = j := by
    by_cases hij : i = j
    · exact .of_forall fun _ _ _ _ _ _ ↦ hij
    obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, res i x ≠ res j x := by
      by_contra! h
      apply hij
      apply AlgHom.toRingHom_injective
      apply IsLocalization.ringHom_ext (𝓞 E)⁰
      ext x
      exact congrArg Subtype.val (h x)
    let a := res i x - res j x
    have ha : a ≠ 0 := sub_ne_zero_of_ne hx
    let d := (Algebra.norm ℤ a).natAbs
    have hd : d ≠ 0 := Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha)
    filter_upwards [d.divisors.finite_toSet.compl_mem_cofinite] with p hp
    intro hprime P hP hPo heq
    have hxP : a ∈ P := Ideal.Quotient.eq.mp (DFunLike.congr_fun heq x)
    exact (hp (Nat.mem_divisors.mpr ⟨spectralLineJet_memLp_false_residueNorm L p hprime P a hxP, hd⟩)).elim
  filter_upwards [Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr (pair i)] with p hp
  exact fun hprime P hP hPo i j ↦ hp i j hprime P hP hPo

/-- Extending scalars bounds the number of residue maps by the rank of the integer ring. -/
private theorem spectralLineJet_memLp_false_integralEmbeddings (E Ω : Type) [Field E] [NumberField E] [Field Ω] :
    Finite (𝓞 E →+* Ω) ∧ Nat.card (𝓞 E →+* Ω) ≤ Module.finrank ℚ E := by
  let e := (RingHom.equivIntAlgHom (𝓞 E) Ω).trans (AlgHom.liftEquiv ℤ Ω (𝓞 E) Ω)
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  rw [Nat.card_congr e, ← RingOfIntegers.rank E]
  simpa only [Module.finrank_baseChange] using card_algHom_le_finrank Ω (Ω ⊗[ℤ] 𝓞 E) Ω

/-- At good primes the degree bound and Galois normality make reduction of embeddings bijective. -/
private theorem spectralLineJet_memLp_false_reductionBijective (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E]
    [IsGalois ℚ L] (ι : E →ₐ[ℚ] L) :
    ∀ᶠ p : ℕ in cofinite, p.Prime → ∀ (P : Ideal (𝓞 L)) (_ : P.IsPrime)
      (_ : P.LiesOver (Ideal.span {(p : ℤ)})) (Ω : Type) [Field Ω] (j : 𝓞 L ⧸ P →+* Ω),
      Function.Injective j → Function.Bijective (fun i : E →ₐ[ℚ] L ↦ j.comp
        ((Ideal.Quotient.mk P).comp (RingOfIntegers.mapRingHom i.toRingHom))) := by
  classical
  filter_upwards [spectralLineJet_memLp_false_reductionInjective L E] with p hp
  intro hp' P hP hPQ Ω _ j hj
  have hcount := spectralLineJet_memLp_false_integralEmbeddings E Ω
  have := hcount.1
  let := Fintype.ofFinite (𝓞 E →+* Ω)
  have hi := (hp hp' P hP hPQ)
  have hinj : Function.Injective (fun i : E →ₐ[ℚ] L ↦ j.comp
      ((Ideal.Quotient.mk P).comp (RingOfIntegers.mapRingHom i.toRingHom))) := by
    intro a b hab
    exact hi (RingHom.ext fun x ↦ hj (DFunLike.congr_fun hab x))
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) ?_⟩
  have he := AlgHom.card_of_splits ℚ E L (fun x ↦ by
    rw [← minpoly.algHom_eq ι ι.injective]
    exact (inferInstance : Normal ℚ L).splits (ι x))
  rw [he, Fintype.card_eq_nat_card]
  exact hcount.2

/-- A residue field of degree d contributes d embeddings exactly when d divides the Frobenius power. -/
private theorem spectralLineJet_memLp_false_finiteFieldMaps (k Ω : Type) [Field k] [Finite k] [Field Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP Ω p] (r : ℕ) :
    let _ := ZMod.algebra k p
    let d := Module.finrank (ZMod p) k
    Nat.card {f : k →+* Ω // ∀ x, (f x) ^ (p ^ r) = f x} = if d ∣ r then d else 0 := by
  classical
  let _ := ZMod.algebra k p
  let _ := ZMod.algebra Ω p
  intro _ d
  have hfixed (f : k →+* Ω) : (∀ x, f x ^ (p ^ r) = f x) ↔ d ∣ r := by
    simp only [← map_pow, f.injective.eq_iff]
    dsimp only [d]
    rw [← FiniteField.orderOf_frobeniusAlgHom (ZMod p) k, orderOf_dvd_iff_pow_eq_one]
    rw [DFunLike.ext_iff]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card,
      AlgHom.one_apply]
  by_cases hr : d ∣ r
  · rw [ite_eq_left hr]
    let e : {f : k →+* Ω // ∀ x, (f x) ^ (p ^ r) = f x} ≃ (k →ₐ[ZMod p] Ω) :=
      { toFun := fun f ↦ ⟨f.1, fun z ↦ DFunLike.congr_fun (Subsingleton.elim
          (f.1.comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) Ω)) z⟩
        invFun := fun f ↦ ⟨f.toRingHom, (hfixed _).mpr hr⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Nat.card_congr e, ← Fintype.card_eq_nat_card]
    exact AlgHom.card_of_splits _ _ _ fun _ ↦ IsAlgClosed.splits _
  · have : IsEmpty {f : k →+* Ω // ∀ x, (f x) ^ (p ^ r) = f x} :=
      ⟨fun f ↦ hr ((hfixed f.val).mp f.property)⟩
    simp [hr]

/-- For a prime ideal the finite-field degree is its inertia degree over the rational prime. -/
private theorem spectralLineJet_memLp_false_residueDegree (E Ω : Type) [Field E] [NumberField E] [Field Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] (P : Ideal (𝓞 E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (r : ℕ) :
    Finite ((𝓞 E ⧸ P) →+* Ω) ∧
    Nat.card {f : (𝓞 E ⧸ P) →+* Ω // ∀ x, (f x) ^ (p ^ r) = f x} =
      if P.inertiaDeg ℤ ∣ r then P.inertiaDeg ℤ else 0 := by
  have hp : p.Prime := Fact.out
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have : P.IsMaximal := Ideal.primesOver.isMaximal (p := q) ⟨P, inferInstance, inferInstance⟩
  let _ := Ideal.Quotient.field P
  have hq₀ : q ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp (by exact_mod_cast hp.ne_zero)
  have : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hq₀ P)
  have : CharP (𝓞 E ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa [q] using (P.mem_of_liesOver q (p : ℤ)).mp (Ideal.subset_span (Set.mem_singleton _)))
  let _ := ZMod.algebra (𝓞 E ⧸ P) p
  have hd : Module.finrank (ZMod p) (𝓞 E ⧸ P) = P.inertiaDeg ℤ := by
    apply Nat.pow_right_injective hp.one_lt
    let _ := Fintype.ofFinite (𝓞 E ⧸ P)
    have hc : Fintype.card (𝓞 E ⧸ P) =
        Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (𝓞 E ⧸ P) := Module.card_eq_pow_finrank
    rw [ZMod.card, Fintype.card_eq_nat_card, ← Ideal.absNorm_eq_natCard, ← Ideal.natAbs_pow_inertiaDeg (p : ℤ) P, Int.natAbs_natCast] at hc
    exact hc.symm
  constructor
  · have := (spectralLineJet_memLp_false_integralEmbeddings E Ω).1
    apply Finite.of_injective (fun f : (𝓞 E ⧸ P) →+* Ω ↦ f.comp (Ideal.Quotient.mk P))
    · intro f g h
      exact RingHom.ext fun y ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact DFunLike.congr_fun h x

  · simpa only [hd] using spectralLineJet_memLp_false_finiteFieldMaps (𝓞 E ⧸ P) Ω p r

/-- A homomorphism from the integer ring to a field of characteristic p factors uniquely through the residue field at its kernel. -/
private theorem spectralLineJet_memLp_false_residueDecomposition (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] :
    ∃ e : (Σ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E), (𝓞 E ⧸ P.val) →+* Ω) ≃ (𝓞 E →+* Ω),
      ∀ P g, e ⟨P,g⟩ = g.comp (Ideal.Quotient.mk P.val) := by
  classical
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let primes (f : 𝓞 E →+* Ω) : q.primesOver (𝓞 E) :=
    ⟨RingHom.ker f, RingHom.ker_isPrime f, ⟨by
      ext a
      change a ∈ Ideal.span {(p : ℤ)} ↔ f (algebraMap ℤ (𝓞 E) a) = 0
      simp [Ideal.mem_span_singleton, CharP.intCast_eq_zero_iff Ω p]⟩⟩
  let Φ (h : Σ P : q.primesOver (𝓞 E), (𝓞 E ⧸ P.val) →+* Ω) := h.2.comp (Ideal.Quotient.mk h.1.val)
  have hpr (P : q.primesOver (𝓞 E)) (g : 𝓞 E ⧸ P.val →+* Ω) : primes (Φ ⟨P,g⟩) = P := by
    have : P.val.IsPrime := P.property.1
    have : P.val.LiesOver q := P.property.2
    have : P.val.IsMaximal := Ideal.primesOver.isMaximal P
    let : Field (𝓞 E ⧸ P.val) := Ideal.Quotient.field _
    apply Subtype.ext
    ext x
    change g (Ideal.Quotient.mk P.val x) = 0 ↔ x ∈ P.val
    rw [map_eq_zero_iff g g.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨P, g⟩ ⟨P', g'⟩ he
      have hs : P = P' := (hpr P g).symm.trans ((congrArg primes he).trans (hpr P' g'))
      subst P'
      congr 1
      apply RingHom.ext
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact DFunLike.congr_fun he x
    · intro f
      exact ⟨⟨primes f, RingHom.kerLift f⟩, RingHom.ext fun _ ↦ rfl⟩
  exact ⟨Equiv.ofBijective Φ hΦ, fun _ _ ↦ rfl⟩

/-- Summing the fixed residue-field embeddings over the primes above p gives the integral point count. -/
private theorem spectralLineJet_memLp_false_residueSum (E Ω : Type) [Field E] [NumberField E] [Field Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] (r : ℕ) :
    Nat.card {f : 𝓞 E →+* Ω // ∀ x, (f x) ^ (p ^ r) = f x} =
      ∑ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E),
        if P.val.inertiaDeg ℤ ∣ r then P.val.inertiaDeg ℤ else 0 := by
  classical
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let B (P : q.primesOver (𝓞 E)) := (𝓞 E ⧸ P.val) →+* Ω
  let A (P : q.primesOver (𝓞 E)) := {f : B P // ∀ x, (f x) ^ (p ^ r) = f x}
  have hA (P : q.primesOver (𝓞 E)) : Finite (B P) ∧
        Nat.card (A P) = if P.val.inertiaDeg ℤ ∣ r then P.val.inertiaDeg ℤ else 0 := by
    have := P.property.1
    have := P.property.2
    exact spectralLineJet_memLp_false_residueDegree E Ω p P.val r
  let (P : q.primesOver (𝓞 E)) : Finite (B P) := (hA P).1
  let (P : q.primesOver (𝓞 E)) : Finite (A P) := Subtype.finite
  obtain ⟨e, he⟩ := spectralLineJet_memLp_false_residueDecomposition E Ω p
  let e₀ : (Σ P, A P) ≃ {a : (Σ P, B P) // ∀ x, a.2 x ^ (p ^ r) = a.2 x} :=
    { toFun := fun ⟨P,f⟩ ↦ ⟨⟨P,f.1⟩,f.2⟩
      invFun := fun ⟨⟨P,f⟩,h⟩ ↦ ⟨P,⟨f,h⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have e₁ : {a : (Σ P, B P) // ∀ x, a.2 x ^ (p ^ r) = a.2 x} ≃
      {f : 𝓞 E →+* Ω // ∀ x, (f x) ^ (p ^ r) = f x} := by
    apply e.subtypeEquiv
    rintro ⟨P,f⟩
    rw [he]
    constructor
    · exact fun h x ↦ h _
    · intro h x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact h y
  rw [← Nat.card_congr (e₀.trans e₁), Nat.card_sigma]
  exact Finset.sum_congr rfl fun P _ ↦ (hA P).2

/-- Prime ideals of norm p to the d correspond to primes over p of inertia degree d. -/
private theorem spectralLineJet_memLp_false_normFibres (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime]
    (d : ℕ) :
    Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = p ^ d} =
      Nat.card {Q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) // Q.val.inertiaDeg ℤ = d} := by
  classical
  have hp : p.Prime := Fact.out
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hq₀ : q ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp (by exact_mod_cast hp.ne_zero)
  have norm (Q : q.primesOver (𝓞 E)) : Q.val.absNorm = p ^ Q.val.inertiaDeg ℤ := by
    have := Q.property.1
    have := Q.property.2
    simpa only [Int.natAbs_natCast] using (Ideal.natAbs_pow_inertiaDeg (p : ℤ) Q.val).symm
  have lies (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (hv : v.asIdeal.absNorm = p ^ d) : v.asIdeal.LiesOver q := by
    have hpow : (p : 𝓞 E) ^ d ∈ v.asIdeal := by simpa [hv] using v.asIdeal.absNorm_mem
    have hle : q ≤ v.asIdeal.under ℤ := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (by
      change algebraMap ℤ (𝓞 E) (p : ℤ) ∈ v.asIdeal
      simpa using v.isPrime.mem_of_pow_mem d hpow))
    exact ⟨hq.eq_of_le (Ideal.comap_isPrime (algebraMap ℤ (𝓞 E)) v.asIdeal).ne_top hle⟩
  apply Nat.card_congr
  refine { toFun := fun v ↦ ⟨⟨v.val.asIdeal, v.val.isPrime, lies v.val v.property⟩,
              Nat.pow_right_injective hp.one_lt ((norm ⟨v.val.asIdeal, v.val.isPrime, lies v.val v.property⟩).symm.trans v.property)⟩
           invFun := fun Q ↦ ⟨⟨Q.val.val, Q.val.property.1, ?_⟩, (norm Q.val).trans (congrArg (p ^ ·) Q.property)⟩
           left_inv := fun _ ↦ rfl
           right_inv := fun _ ↦ rfl }
  have := Q.val.property.2
  exact Ideal.ne_bot_of_liesOver_of_ne_bot hq₀ Q.val.val

/-- Group the prime-ideal count into its inertia-degree fibres. -/
private theorem spectralLineJet_memLp_false_normSum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime]
    (r : ℕ) (hr : 0 < r) :
    (∑ d ∈ r.divisors, d * Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
        v.asIdeal.absNorm = p ^ d}) =
      ∑ P : (Ideal.span {(p : ℤ)}).primesOver (𝓞 E),
        if P.val.inertiaDeg ℤ ∣ r then P.val.inertiaDeg ℤ else 0 := by
  classical
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have weight (d : ℕ) :
      d * Nat.card {Q : q.primesOver (𝓞 E) // Q.val.inertiaDeg ℤ = d} =
        ∑ Q : q.primesOver (𝓞 E), if Q.val.inertiaDeg ℤ = d then d else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [Nat.mul_comm]
  have hw (d : ℕ) : d * Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
      v.asIdeal.absNorm = p ^ d} = ∑ Q : q.primesOver (𝓞 E), if Q.val.inertiaDeg ℤ = d then d else 0 :=
    (congrArg (d * ·) (spectralLineJet_memLp_false_normFibres E p d)).trans (weight d)
  rw [Finset.sum_congr rfl fun d _ ↦ hw d, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q _
  simp [Nat.mem_divisors, hr.ne']

/-- Through reduction, composition with the r-th Frobenius power acts by raising each value to p to the r. -/
private theorem spectralLineJet_memLp_false_frobeniusOrbits (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E]
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : L ≃ₐ[ℚ] L) (hσ : IsArithFrobAt ℤ σ P) (Ω : Type) [Field Ω] (j : 𝓞 L ⧸ P →+* Ω)
    (r : ℕ) :
    let red (i : E →ₐ[ℚ] L) := j.comp ((Ideal.Quotient.mk P).comp (RingOfIntegers.mapRingHom i.toRingHom))
    Function.Bijective red →
    Nat.card {i : E →ₐ[ℚ] L // (σ ^ r).toAlgHom.comp i = i} =
      Nat.card {f : 𝓞 E →+* Ω // ∀ x, (f x) ^ (p ^ r) = f x} := by
  intro red he
  have hq : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [← P.over_def (Ideal.span {(p : ℤ)}), Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv,
      Nat.card_zmod]
  have hp (x : 𝓞 L) : Ideal.Quotient.mk P (σ • x) = (Ideal.Quotient.mk P x) ^ p := by
    rw [← hq]
    exact hσ.mk_apply x
  have hpow (n : ℕ) (x : 𝓞 L) :
      Ideal.Quotient.mk P (σ ^ n • x) = (Ideal.Quotient.mk P x) ^ (p ^ n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_smul, hp, ih, ← pow_mul, pow_succ]
  have eq (i : E →ₐ[ℚ] L) (x : 𝓞 E) : red ((σ ^ r).toAlgHom.comp i) x = (red i x) ^ (p ^ r) := by
    change j (Ideal.Quotient.mk P ((σ ^ r) • (RingOfIntegers.mapRingHom i.toRingHom x))) = _
    rw [hpow, map_pow]
    rfl
  apply Nat.card_congr
  let e := Equiv.ofBijective red he
  apply e.subtypeEquiv
  intro i
  constructor
  · intro hi x
    change (red i x) ^ (p ^ r) = red i x
    simpa only [hi] using (eq i x).symm
  · intro h
    exact he.1 (RingHom.ext fun x ↦ (eq i x).trans (h x))

/-- Outside finitely many primes, the residue-field point count equals the number of embeddings
fixed by a Frobenius power. Reduction is bijective there and respects the Frobenius action. -/
private theorem spectralLineJet_memLp_false_frobeniusTrace
    (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [IsGalois ℚ L]
    (_ι : Nonempty (E →ₐ[ℚ] L)) :
    ∃ B : Finset ℕ, ∀ p ∉ B, p.Prime → ∀ (P : Ideal (𝓞 L)), P.IsPrime →
      P.LiesOver (Ideal.span {(p : ℤ)}) → ∀ σ : L ≃ₐ[ℚ] L, IsArithFrobAt ℤ σ P →
      ∀ r : ℕ, 0 < r →
        (∑ d ∈ r.divisors, d * Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) //
          v.asIdeal.absNorm = p ^ d}) =
          Nat.card {i : E →ₐ[ℚ] L // ((σ ^ r).toAlgHom.comp i) = i} := by
  classical
  obtain ⟨ι⟩ := _ι
  have hgood := Filter.eventually_cofinite.mp (spectralLineJet_memLp_false_reductionBijective L E ι)
  refine ⟨hgood.toFinset, fun p hpB hp P hP hPQ σ hσ r hr ↦ ?_⟩
  have hgoodp := not_not.mp (fun hn ↦ hpB (hgood.mem_toFinset.mpr hn))
  have : Fact p.Prime := ⟨hp⟩
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have : P.IsMaximal := Ideal.primesOver.isMaximal (p := q) ⟨P, hP, hPQ⟩
  let _ := Ideal.Quotient.field P
  have : CharP (𝓞 L ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa [q] using (P.mem_of_liesOver q (p : ℤ)).mp (Ideal.subset_span (Set.mem_singleton _)))
  let Ω := AlgebraicClosure (𝓞 L ⧸ P)
  let j := algebraMap (𝓞 L ⧸ P) Ω
  have : CharP Ω p := charP_of_injective_algebraMap j.injective p
  exact (spectralLineJet_memLp_false_normSum E p r hr).trans ((spectralLineJet_memLp_false_residueSum E Ω p r).symm.trans
    (spectralLineJet_memLp_false_frobeniusOrbits L E p P σ hσ Ω j r (hgoodp hp P hP hPQ Ω j j.injective)).symm)

end

/-- Outside finitely many rational primes, the counts of residue-field points
in an S₃ splitting field and its two subfields are fixed-point counts for
one Frobenius power acting on their embeddings. The trace for E is the
sum of d times the number of prime ideals of norm p ^ d over d dividing r. -/
private theorem spectralLineJet_memLp_false_frobenius
    (L k K : Type) [Field L] [NumberField L] [Field k] [NumberField k] [Field K] [NumberField K]
    [IsGalois ℚ L] (G : (L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (ιK : Nonempty (K →ₐ[ℚ] L)) :
    ∃ B : Finset ℕ, ∀ p ∉ B, p.Prime → ∀ r : ℕ, 0 < r →
      let trace := fun (E : Type) [Field E] [NumberField E] ↦ ∑ d ∈ r.divisors, d *
        Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = p ^ d}
      ∃ τ : Equiv.Perm (Fin 3),
        trace L = (Finset.univ.filter fun g : Equiv.Perm (Fin 3) ↦ τ * g = g).card ∧
        trace k = Nat.card {i : k →ₐ[ℚ] L // (G.symm τ).toAlgHom.comp i = i} ∧
        trace K = Nat.card {i : K →ₐ[ℚ] L // (G.symm τ).toAlgHom.comp i = i} := by
  classical
  obtain ⟨BL, hL⟩ := spectralLineJet_memLp_false_frobeniusTrace L L ⟨AlgHom.id ℚ L⟩
  obtain ⟨Bk, hk⟩ := spectralLineJet_memLp_false_frobeniusTrace L k ιk
  obtain ⟨BK, hK⟩ := spectralLineJet_memLp_false_frobeniusTrace L K ιK
  refine ⟨(BL ∪ Bk) ∪ BK, fun p hpB hp r hr ↦ ?_⟩
  simp only [Finset.mem_union, not_or] at hpB
  obtain ⟨P, hP, hPp, σ, hσ⟩ := spectralLineJet_memLp_false_frobeniusLift L p hp
  let g := σ ^ r
  let e := (Algebra.IsAlgebraic.algEquivEquivAlgHom ℚ L).symm.toEquiv.trans G.toEquiv
  have he (i : L →ₐ[ℚ] L) : G g * e i = e (g.toAlgHom.comp i) := by
    change G g * G _ = G _
    rw [← map_mul]
    exact congrArg G (AlgEquiv.ext fun x ↦ rfl)
  refine ⟨G g, (hL p hpB.1.1 hp P hP hPp σ hσ r hr).trans
    (spectralLineJet_memLp_false_fixedCount e _ (G g * ·) he), ?_, ?_⟩
  · simpa [g] using hk p hpB.1.2 hp P hP hPp σ hσ r hr
  · simpa [g] using hK p hpB.2 hp P hP hPp σ hσ r hr

/-- Prime norms over a finite set of excluded rational primes divide one
of the finitely many norms of the principal ideals generated by those primes. -/
private theorem spectralLineJet_memLp_false_badNorm (E : Type) [Field E] [NumberField E] (B : Finset ℕ)
    (p d : ℕ) (hp : p.Prime) (hmem : p ∈ B)
    (hn : p ^ d ∉ B.biUnion fun q ↦ (q ^ Module.finrank ℤ (𝓞 E)).divisors) :
    Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = p ^ d} = 0 := by
  classical
  have : IsEmpty {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = p ^ d} := ⟨by
    rintro ⟨v, hv⟩
    have hpow : (p : 𝓞 E) ^ d ∈ v.asIdeal := by simpa [hv] using v.asIdeal.absNorm_mem
    have hle : Ideal.span {(p : 𝓞 E)} ≤ v.asIdeal :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (v.isPrime.mem_of_pow_mem d hpow))
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_natCast, hv] at hdvd
    exact hn (Finset.mem_biUnion.mpr ⟨p, hmem, Nat.mem_divisors.mpr ⟨hdvd, pow_ne_zero _ hp.ne_zero⟩⟩)⟩
  simp

/-- The unramified Frobenius traces determine the prime-ideal counts
outside finitely many exceptional norms. -/
private theorem spectralLineJet_memLp_false_primeCounts
    (L k K : Type) [Field L] [NumberField L] [Field k] [NumberField k] [Field K] [NumberField K]
    [IsGalois ℚ L]
    (hG : Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)))
    (ιk : Nonempty (k →ₐ[ℚ] L)) (hkdeg : Module.finrank ℚ k = 2)
    (ιK : Nonempty (K →ₐ[ℚ] L)) (hKdeg : Module.finrank ℚ K = 3) :
    let count := fun (E : Type) [Field E] [NumberField E] (n : ℕ) ↦
      Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) // v.asIdeal.absNorm = n}
    ∃ A : Finset ℕ, (∀ n ∈ A, 1 < n) ∧
      ∀ n ∉ A, count L n + 2 * count ℚ n = count k n + 2 * count K n := by
  classical
  intro count
  let G := hG.some
  obtain ⟨B, hF⟩ := spectralLineJet_memLp_false_frobenius L k K G ιk ιK
  let bad := fun (E : Type) [Field E] [NumberField E] ↦
    B.biUnion fun p ↦ (p ^ Module.finrank ℤ (𝓞 E)).divisors
  let A := (bad L ∪ bad ℚ) ∪ (bad k ∪ bad K)
  refine ⟨A.filter (1 < ·), fun n hn ↦ (Finset.mem_filter.mp hn).2, fun n hnA ↦ ?_⟩
  by_cases hn : IsPrimePow n
  · obtain ⟨p, r, hp, hr, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    have hnorm : 1 < p ^ r := one_lt_pow₀ hp.one_lt hr.ne'
    have hout : p ^ r ∉ A := fun h ↦ hnA (Finset.mem_filter.mpr ⟨h, hnorm⟩)
    by_cases hpB : p ∈ B
    · simp only [A, Finset.mem_union, not_or] at hout
      have hbad (E : Type) [Field E] [NumberField E] (he : p ^ r ∉ bad E) :
          count E (p ^ r) = 0 := spectralLineJet_memLp_false_badNorm E B p r hp hpB he
      rw [hbad L hout.1.1, hbad ℚ hout.1.2, hbad k hout.2.1, hbad K hout.2.2]
    apply spectralLineJet_memLp_false_invertTraces
      (fun d ↦ count L (p ^ d) + 2 * count ℚ (p ^ d))
      (fun d ↦ count k (p ^ d) + 2 * count K (p ^ d)) _ r hr
    intro j hj
    let trace := fun (E : Type) [Field E] [NumberField E] ↦
      ∑ d ∈ j.divisors, d * count E (p ^ d)
    obtain ⟨τ, hL, hk, hK⟩ := hF p hpB hp j hj
    obtain ⟨ek, φ, heφ, hφ⟩ := spectralLineJet_memLp_false_embeddingAction L k ιk.some 2 hkdeg
    obtain ⟨eK, ψ, heψ, hψ⟩ := spectralLineJet_memLp_false_embeddingAction L K ιK.some 3 hKdeg
    have transitive {n : ℕ} (f : (L ≃ₐ[ℚ] L) →* Equiv.Perm (Fin n))
        (hf : ∀ i j, ∃ g, f g i = j) (i j : Fin n) :
        ∃ g, (f.comp G.symm.toMonoidHom) g i = j := by
      obtain ⟨g, hg⟩ := hf i j
      exact ⟨G g, by simpa using hg⟩
    change trace L = _ at hL
    change trace k = _ at hk
    change trace K = _ at hK
    have hQ : trace ℚ = 1 := spectralLineJet_memLp_false_ratTrace p j hp hj
    have hχ := spectralLineJet_memLp_false_transitiveCharacters
      (φ.comp G.symm.toMonoidHom) (ψ.comp G.symm.toMonoidHom) (transitive φ hφ) (transitive ψ hψ) τ
    have hk' := hk.trans ((spectralLineJet_memLp_false_fixedCount ek _ _ (heφ (G.symm τ))).trans hχ.1)
    have hK' := hK.trans ((spectralLineJet_memLp_false_fixedCount eK _ _ (heψ (G.symm τ))).trans hχ.2)
    have he : trace L + 2 * trace ℚ = trace k + 2 * trace K := by
      simpa only [hL, hQ, hk', hK', mul_one] using spectralLineJet_memLp_false_character τ
    simpa only [trace, Nat.mul_add, Finset.sum_add_distrib, Nat.mul_left_comm _ 2,
      ← Finset.mul_sum] using he
  · have h (E : Type) [Field E] [NumberField E] : count E n = 0 :=
      spectralLineJet_memLp_false_countSupport E n hn
    simp [h]

section CubicZeroCount

open Complex Bornology Metric IsDedekindDomain

local notation "ζChar(" E ")" => (1 : PontryaginDual C𝔽(E))
local notation "completedζ(" E ")" => continuedCompletedHeckeL ζChar(E)
local notation "finiteζ(" E ")" => (finiteHeckeL_exists_continuation ζChar(E)).choose
local notation "ζRatio(" E ")" => toMeromorphicNFOn (completedζ(ℚ) / completedζ(E)) univ

/-- A bound on all four sides of a rectangle bounds the value at the real point one. -/
private theorem cubicZeroCount_rectangle (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {R lo hi C : ℝ} (hR : 1 < R) (hl : lo < 0) (hh : 0 < hi)
    (hv : ∀ z : ℂ, z.re = -R ∨ z.re = R → ‖f z‖ ≤ C)
    (hy : ∀ z : ℂ, |z.re| ≤ R → z.im = lo ∨ z.im = hi → ‖f z‖ ≤ C) :
    ‖f 1‖ ≤ C := by
  have hR' : -R < R := by linarith
  have hT : lo < hi := hl.trans hh
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo (-R) R).reProdIm (isBounded_Ioo lo hi)) hf.diffContOnCl
  · intro z hz
    rw [Complex.frontier_reProdIm, closure_Ioo hR'.ne, frontier_Ioo hT,
      closure_Ioo hT.ne, frontier_Ioo hR'] at hz
    rcases hz with hz | hz
    · exact hy z (abs_le.mpr hz.1) hz.2
    · exact hv z hz.1
  · rw [Complex.closure_reProdIm, closure_Ioo hR'.ne, closure_Ioo hT.ne]
    exact ⟨⟨by simp; linarith, by simpa using hR.le⟩, by simpa using And.intro hl.le hh.le⟩

/-- Norm of the Gaussian used on a box of half-width R. -/
private theorem cubicZeroCount_gaussianNorm {R : ℝ} (z : ℂ) :
    ‖(Complex.exp (z ^ 2 / (R : ℂ)))‖ = Real.exp ((z.re ^ 2 - z.im ^ 2) / R) := by
  simp only [Complex.norm_exp, Complex.div_ofReal_re, pow_two, Complex.mul_re]

/-- For fixed R the Gaussian kills any exponential in the height on horizontal edges. -/
private theorem cubicZeroCount_gaussianHorizontal {R A B C : ℝ} (hR : 0 < R) (hA : 0 < A) (hC : 0 < C) :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, |z.re| ≤ R → T ≤ |z.im| →
      (A * Real.exp (B * |z.im|)) * ‖(Complex.exp (z ^ 2 / (R : ℂ)))‖ ≤ C := by
  let T := max 1 (max ((B + 1) * R) (R - Real.log (C / A)))
  refine ⟨T, lt_of_lt_of_le zero_lt_one (le_max_left ..), ?_⟩
  intro z hx hy
  have hy₁ : (B + 1) * R ≤ |z.im| := (le_trans (le_max_left ..) (le_max_right ..)).trans hy
  have hy₂ : R - Real.log (C / A) ≤ |z.im| := (le_trans (le_max_right ..) (le_max_right ..)).trans hy
  have hs : z.re ^ 2 ≤ R ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.re) hx 2
  have hs' := mul_le_mul_of_nonneg_right hy₁ (abs_nonneg z.im)
  rw [← sq, sq_abs] at hs'
  have he : B * |z.im| + (z.re ^ 2 - z.im ^ 2) / R ≤ Real.log (C / A) := by
    rw [← le_sub_iff_add_le', div_le_iff₀ hR]
    nlinarith [mul_le_mul_of_nonneg_right hy₂ hR.le]
  rw [cubicZeroCount_gaussianNorm, mul_assoc, ← Real.exp_add]
  calc A * Real.exp _ ≤ A * Real.exp (Real.log (C / A)) := by gcongr
       _ = C := by rw [Real.exp_log (div_pos hC hA)]; field_simp

/-- On a vertical edge, completing the square makes the Gaussian cost only an exponential in R. -/
private theorem cubicZeroCount_gaussianVertical {R B : ℝ} (hR : 0 < R) (z : ℂ) (hx : |z.re| ≤ R) :
    Real.exp (B * |z.im|) * ‖(Complex.exp (z ^ 2 / (R : ℂ)))‖ ≤ Real.exp (R * (1 + B ^ 2)) := by
  rw [cubicZeroCount_gaussianNorm, ← Real.exp_add, Real.exp_le_exp]
  have hx' : z.re ^ 2 ≤ R ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.re) hx 2
  have hs := sq_nonneg (|z.im| - 2⁻¹ * B * R)
  rw [← le_sub_iff_add_le', div_le_iff₀ hR]
  nlinarith [sq_abs z.im, sq_nonneg (B * R)]

/-- An entire quotient cannot have uniform factorial savings on both distant
vertical lines, even if its known horizontal estimates hold only along two
sequences depending on the strip. The point tested is the real parameter 1. -/
private theorem cubicZeroCount_factorialEdges (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (D B : ℝ) (hD : 0 < D)
    (hedge : ∀ (n : ℕ) (z : ℂ), |z.re| = 2 * (n + 1 : ℝ) →
      ‖f z‖ ≤ D ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |z.im|))
    (hhor : ∀ n : ℕ, ∃ A > 0, ∃ b : ℝ, ∀ S > (0 : ℝ), ∃ lo hi : ℝ,
      lo < -S ∧ S < hi ∧ ∀ z : ℂ, |z.re| ≤ 2 * (n + 1 : ℝ) →
        z.im = lo ∨ z.im = hi → ‖f z‖ ≤ A * Real.exp (b * |z.im|)) :
    f 1 = 0 := by
  let c := D * Real.exp (2 * (1 + B ^ 2))
  have hc : 0 < c := mul_pos hD (Real.exp_pos _)
  have line (n : ℕ) : ‖f 1‖ ≤ c ^ (n + 1) / (n.factorial : ℝ) := by
    let R : ℝ := 2 * (n + 1 : ℝ)
    let V : ℝ := c ^ (n + 1) / (n.factorial : ℝ)
    have hR : 1 < R := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hR0 : 0 < R := zero_lt_one.trans hR
    have hV : 0 < V := by dsimp [V]; positivity
    obtain ⟨A, hA, b, hy⟩ := hhor n
    obtain ⟨S, hS, hsmall⟩ := cubicZeroCount_gaussianHorizontal (B := b) hR0 hA hV
    obtain ⟨lo, hi, hlo, hhi, hh⟩ := hy S hS
    have hrect : ‖f 1 * (Complex.exp ((1 : ℂ) ^ 2 / (R : ℂ)))‖ ≤ V := by
      apply cubicZeroCount_rectangle (fun z ↦ f z * (Complex.exp (z ^ 2 / (R : ℂ)))) (hf.mul (by fun_prop)) hR
        (by linarith : lo < 0) (by linarith : 0 < hi)
      · intro z hx
        have heq : |z.re| = R := hx.elim (fun h ↦ by rw [h, abs_neg, abs_of_pos hR0])
          (fun h ↦ by rw [h, abs_of_pos hR0])
        rw [norm_mul]
        calc
          _ ≤ (D ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |z.im|)) * ‖(Complex.exp (z ^ 2 / (R : ℂ)))‖ :=
            mul_le_mul_of_nonneg_right (hedge n z heq) (norm_nonneg _)
          _ ≤ (D ^ (n + 1) / (n.factorial : ℝ)) * Real.exp (R * (1 + B ^ 2)) := by
            rw [mul_assoc]; gcongr; exact cubicZeroCount_gaussianVertical hR0 z heq.le
          _ = V := by
            have e : R * (1 + B ^ 2) = (n + 1 : ℕ) * (2 * (1 + B ^ 2)) := by push_cast; dsimp [R]; ring
            rw [e, Real.exp_nat_mul]
            dsimp [V, c]; rw [mul_pow]; ring
      · intro z hx hz
        rw [norm_mul]
        apply (mul_le_mul_of_nonneg_right (hh z hx hz) (norm_nonneg _)).trans
        apply hsmall z hx
        rcases hz with h | h
        · rw [h, abs_of_neg (by linarith : lo < 0)]; linarith
        · rw [h, abs_of_pos (by linarith : 0 < hi)]; exact hhi.le
    apply le_trans _ hrect
    rw [norm_mul]
    apply le_mul_of_one_le_right (norm_nonneg _)
    rw [cubicZeroCount_gaussianNorm, Real.one_le_exp_iff]
    simp [hR0.le]
  have hlim : Tendsto (fun n : ℕ ↦ c ^ (n + 1) / (n.factorial : ℝ)) atTop (𝓝 0) := by
    simpa [pow_succ, mul_div_right_comm] using (FloorSemiring.tendsto_pow_div_factorial_atTop c).mul_const c
  exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall line))

/-- One step of the real gamma recurrence, valid also at a zero of its reciprocal. -/
private theorem cubicZeroCount_gammaStep (s : ℂ) :
    ‖s‖ * ‖(Gammaℝ (s + 2))⁻¹‖ = (2 * Real.pi) * ‖(Gammaℝ s)⁻¹‖ := by
  by_cases hs : s = 0
  · subst s; simp [Gammaℝ_def]
  have he : (s * (Gammaℝ (s + 2))⁻¹) = (2 * (Real.pi : ℂ)) * (Gammaℝ s)⁻¹ := by
    rw [Gammaℝ_add_two hs]; field_simp [hs]
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.pi_pos.le] using congrArg norm he

/-- Gamma recursion on integer-spaced vertical contours gives factorial decay of its inverse. -/
private theorem cubicZeroCount_gammaRecurrence (s : ℂ) (hs : 2 ≤ s.re) (n : ℕ) :
    (n.factorial : ℝ) * ‖(Gammaℝ (s + 2 * n))⁻¹‖ ≤ (2 * Real.pi) ^ n * ‖(Gammaℝ s)⁻¹‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    let w := s + 2 * (n : ℂ)
    have hw : (n + 1 : ℝ) ≤ ‖w‖ := by
      apply le_trans _ (re_le_norm w)
      dsimp [w]
      simp only [mul_re, re_ofNat, natCast_re, im_ofNat, zero_mul, sub_zero]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hs' : s + 2 * (n.succ : ℂ) = w + 2 := by dsimp [w]; push_cast; ring
    rw [hs', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    calc
      ((n : ℝ) + 1) * (n.factorial : ℝ) * ‖(Gammaℝ (w + 2))⁻¹‖ =
          (n.factorial : ℝ) * (((n : ℝ) + 1) * ‖(Gammaℝ (w + 2))⁻¹‖) := by ring
      _ ≤ (n.factorial : ℝ) * (‖w‖ * ‖(Gammaℝ (w + 2))⁻¹‖) := by gcongr
      _ = (2 * Real.pi) * ((n.factorial : ℝ) * ‖(Gammaℝ w)⁻¹‖) := by rw [cubicZeroCount_gammaStep]; ring
      _ ≤ _ := by calc
                    _ ≤ (2 * Real.pi) * ((2 * Real.pi) ^ n * ‖(Gammaℝ s)⁻¹‖) := by gcongr
                    _ = _ := by ring

/-- On a bounded positive strip the reciprocal real gamma factor grows at most exponentially. -/
private theorem cubicZeroCount_gammaPositiveStrip (a b : ℝ) (ha : 0 < a) :
    ∃ A > 0, ∃ B : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖(Gammaℝ z)⁻¹‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨A, hA, h⟩ := exists_norm_inv_GammaReal_add_le_on_strip a b ha 0 (by simp)
  refine ⟨A, hA, 1 + Real.pi / 4, fun z hz ↦ ?_⟩
  have h₀ : ‖(Gammaℝ z)⁻¹‖ ≤ A * ((1 + |z.im|) * Real.exp (Real.pi * |z.im|/4)) := by simpa using h z hz
  apply h₀.trans
  gcongr
  calc
    (1 + |z.im|) * Real.exp (Real.pi * |z.im|/4) ≤ Real.exp |z.im| * Real.exp (Real.pi * |z.im|/4) := by
      gcongr; linarith [Real.add_one_le_exp |z.im|]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- On every fixed vertical strip the reciprocal real gamma factor grows at most exponentially. -/
private theorem cubicZeroCount_gammaStrip (a b : ℝ) :
    ∃ A > 0, ∃ B : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖(Gammaℝ z)⁻¹‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  have haux (k : ℕ) (a b : ℝ) (hk : 0 < a + 2 * k) :
      ∃ A > 0, ∃ B : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖(Gammaℝ z)⁻¹‖ ≤ A * Real.exp (B * |z.im|) := by
    induction k generalizing a b with
    | zero => exact cubicZeroCount_gammaPositiveStrip a b (by simpa using hk)
    | succ k ih =>
      obtain ⟨A, hA, B, h⟩ := ih (a + 2) (b + 2) (by push_cast at hk; linarith)
      let C := 1 + |a| + |b|
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨C * A, mul_pos hC hA, 1 + B, fun z hz ↦ ?_⟩
      have hz' : (z + 2).re ∈ Icc (a + 2) (b + 2) := by simpa using hz
      have hRe : |z.re| ≤ |a| + |b| := abs_le.mpr
        ⟨by linarith [hz.1, neg_abs_le a, abs_nonneg b], by linarith [hz.2, le_abs_self b, abs_nonneg a]⟩
      have hzN : ‖z‖ ≤ C * Real.exp |z.im| := by
        apply (Complex.norm_le_abs_re_add_abs_im z).trans
        calc _ ≤ C * (1 + |z.im|) := by dsimp [C]; nlinarith [mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) (abs_nonneg z.im)]
             _ ≤ _ := by gcongr; linarith [Real.add_one_le_exp |z.im|]
      have hu := (h (z + 2) hz')
      simp only [Complex.add_im, Complex.im_ofNat, add_zero] at hu
      calc
        _ ≤ (2 * Real.pi) * ‖(Gammaℝ z)⁻¹‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.pi_gt_three])
        _ = ‖z‖ * ‖(Gammaℝ (z + 2))⁻¹‖ := (cubicZeroCount_gammaStep z).symm
        _ ≤ (C * Real.exp |z.im|) * (A * Real.exp (B * |z.im|)) := by gcongr
        _ = _ := by rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring
  exact haux n a b (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- The completed Dedekind zeta function has the same order at reflected points. -/
private theorem cubicZeroCount_reflectedOrder (E : Type) [Field E] [NumberField E] (z : ℂ) :
    meromorphicOrderAt completedζ(E) (1 - z) = meromorphicOrderAt completedζ(E) z := by
  obtain ⟨hL, ha⟩ := continuedCompletedHeckeL_spec ζChar(E)
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation ζChar(E) _ _ hL ha hL (by simpa using ha)
  have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (f := completedζ(E))
    (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
    (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show completedζ(E) ∘ (fun s : ℂ ↦ 1 - s) = ε * completedζ(E) from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at hc
  exact hc.symm

/-- Except at its two poles, the completed Dedekind zeta function has order zero outside the open strip. -/
private theorem cubicZeroCount_exteriorOrder (E : Type) [Field E] [NumberField E] (z : ℂ)
    (h : z.re ≤ 0 ∨ 1 ≤ z.re) (hz : z ≠ 0) (hz' : z ≠ 1) :
    meromorphicOrderAt completedζ(E) z = 0 := by
  obtain ⟨hm, ha⟩ := continuedCompletedHeckeL_spec ζChar(E)
  have hpos := (completedHeckeL_one_analyticOnNhd _ hm ha z (by simp [hz, hz'])).meromorphicOrderAt_nonneg
  refine le_antisymm (le_of_not_gt fun hn ↦ ?_) hpos
  rcases h with hl | hr
  · have hc : 0 < meromorphicOrderAt completedζ(E) (1 - z) := (cubicZeroCount_reflectedOrder E z).symm ▸ hn
    have hs : 0 < (1 - z).re := by simp; linarith
    have ht := completedHeckeL_continuation_zeros ζChar(E) _ hm ha hs hc
    simp at ht; linarith
  · exact (not_lt_of_ge hr) (completedHeckeL_continuation_zeros ζChar(E) _ hm ha (by linarith) hn)

/-- The two poles of the completed trivial character are simple. -/
private theorem cubicZeroCount_poles (E : Type) [Field E] [NumberField E] :
    meromorphicOrderAt completedζ(E) 0 = -1 ∧ meromorphicOrderAt completedζ(E) 1 = -1 := by
  obtain ⟨hm, ha⟩ := continuedCompletedHeckeL_spec ζChar(E)
  obtain ⟨t, ⟨_, h₀, h₁, _⟩, _⟩ := completedHeckeL_continuation_simplePoles ζChar(E) _ hm ha rfl
  have ht : I * (t : ℂ) = 0 := by
    by_contra hn
    have hn' : I * (t : ℂ) ≠ 1 := fun e ↦ by simpa [mul_re] using congrArg re e
    have hmem : I * (t : ℂ) ∈ ({0, 1}ᶜ : Set ℂ) := by simpa using And.intro hn hn'
    have h := (completedHeckeL_one_analyticOnNhd _ hm ha _ hmem).meromorphicOrderAt_nonneg
    rw [h₀] at h
    exact (WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)).not_ge h
  simpa only [ht, add_zero] using And.intro h₀ h₁

/-- If the cubic zero orders are dominated throughout the strip, the quotient of the two completed
functions is entire. Their two poles cancel. -/
private theorem cubicZeroCount_entireQuotient (K : Type) [Field K] [NumberField K]
    (h : ∀ z : ℂ, 0 < z.re → z.re < 1 → order(ζChar(K), z) ≤ order(ζChar(ℚ), z)) :
    Differentiable ℂ ζRatio(K) := by
  intro z
  have hQ := continuedCompletedHeckeL_spec ζChar(ℚ)
  have hK := continuedCompletedHeckeL_spec ζChar(K)
  apply AnalyticAt.differentiableAt
  rw [← (meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn (hQ.1.meromorphicOn.div hK.1.meromorphicOn) (mem_univ _),
    meromorphicOrderAt_div (hQ.1.meromorphicOn z (mem_univ _)) (hK.1.meromorphicOn z (mem_univ _))]
  by_cases h0 : z = 0
  · subst z; rw [(cubicZeroCount_poles ℚ).1, (cubicZeroCount_poles K).1]; decide
  by_cases h1 : z = 1
  · subst z; rw [(cubicZeroCount_poles ℚ).2, (cubicZeroCount_poles K).2]; decide
  by_cases hs : 0 < z.re ∧ z.re < 1
  · rw [spectralLineJet_memLp_false_stripOrder ℚ z hs.1 hs.2, spectralLineJet_memLp_false_stripOrder K z hs.1 hs.2]
    change (0 : WithTop ℤ) ≤ ((order(ζChar(ℚ), z) : ℤ) : WithTop ℤ) - ((order(ζChar(K), z) : ℤ) : WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (Int.ofNat_le.mpr (h z hs.1 hs.2)))
  · have he : z.re ≤ 0 ∨ 1 ≤ z.re := by grind
    rw [cubicZeroCount_exteriorOrder ℚ z he h0 h1, cubicZeroCount_exteriorOrder K z he h0 h1]; decide

/-- In both possible cubic signatures, cancellation leaves two reciprocal real gamma factors. -/
private theorem cubicZeroCount_eulerFactors (K : Type) [Field K] [NumberField K] (hd : Module.finrank ℚ K = 3) :
    ∃ (c w : ℝ), 0 < c ∧ 0 ≤ w ∧ w ≤ 1 ∧ ∀ s : ℂ, 1 < s.re →
      completedζ(ℚ) s / completedζ(K) s = c * (Gammaℝ s)⁻¹ * (Gammaℝ (s + (w : ℂ)))⁻¹ * (finiteζ(ℚ) s / finiteζ(K) s) := by
  have sig := InfinitePlace.card_add_two_mul_card_eq_rank K
  have sigQ := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (K := ℚ) (by simp)
  have sigQ' := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (K := ℚ) (by simp)
  have hs (s : ℂ) (h : 1 < s.re) (E : Type) [Field E] [NumberField E] :
      completedζ(E) s = heckeGammaFactor ζChar(E) s * finiteζ(E) s := by
    rw [(continuedCompletedHeckeL_spec ζChar(E)).2 ⟨s, h⟩, (finiteHeckeL_exists_continuation ζChar(E)).choose_spec.2 ⟨s, h⟩]
    rfl
  have hcase : (InfinitePlace.nrRealPlaces K = 3 ∧ InfinitePlace.nrComplexPlaces K = 0) ∨
      (InfinitePlace.nrRealPlaces K = 1 ∧ InfinitePlace.nrComplexPlaces K = 1) := by omega
  rcases hcase with ⟨hr, hc⟩ | ⟨hr, hc⟩
  · refine ⟨1, 0, by norm_num, by norm_num, by norm_num, fun s h ↦ ?_⟩
    have hg : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [hs s h ℚ, hs s h K, heckeGammaFactor_one, heckeGammaFactor_one, sigQ, sigQ', hr, hc]
    simp only [pow_one, pow_zero, mul_one, ofReal_one, ofReal_zero, add_zero, one_mul]
    generalize Gammaℝ s = g at hg ⊢
    generalize finiteζ(ℚ) s = x
    generalize finiteζ(K) s = y
    by_cases hy : y = 0
    · simp [hy]
    · field_simp
  · refine ⟨2, 1, by norm_num, by norm_num, by norm_num, fun s h ↦ ?_⟩
    have hg : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [hs s h ℚ, hs s h K, heckeGammaFactor_one, heckeGammaFactor_one, sigQ, sigQ', hr, hc,
      ← Gammaℝ_mul_Gammaℝ_add_one]
    simp only [pow_one, pow_zero, mul_one, ofReal_ofNat, ofReal_one]
    have hg' : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    generalize Gammaℝ s = g at hg ⊢
    generalize Gammaℝ (s + 1) = g' at hg' ⊢
    generalize finiteζ(ℚ) s = x
    generalize finiteζ(K) s = y
    by_cases hy : y = 0
    · simp [hy]
    · field_simp

/-- Continue the Euler factorization to every regular point of the finite quotient. -/
private theorem cubicZeroCount_finiteQuotient (K : Type) [Field K] [NumberField K] (c w : ℝ)
    (he : ∀ s : ℂ, 1 < s.re →
      completedζ(ℚ) s / completedζ(K) s = c * (Gammaℝ s)⁻¹ * (Gammaℝ (s + (w : ℂ)))⁻¹ * (finiteζ(ℚ) s / finiteζ(K) s))
    (s : ℂ) (hQ : AnalyticAt ℂ finiteζ(ℚ) s) (hK : AnalyticAt ℂ finiteζ(K) s) (hne : finiteζ(K) s ≠ 0) :
    ζRatio(K) s = c * (Gammaℝ s)⁻¹ * (Gammaℝ (s + (w : ℂ)))⁻¹ * (finiteζ(ℚ) s / finiteζ(K) s) := by
  let G (z : ℂ) := (c : ℂ) * (Gammaℝ z)⁻¹ * (Gammaℝ (z + w))⁻¹
  have hG : Differentiable ℂ G := (differentiable_Gammaℝ_inv.const_mul (c : ℂ)).mul
    (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const _))
  have hm := (continuedCompletedHeckeL_spec ζChar(ℚ)).1.meromorphicOn.div (continuedCompletedHeckeL_spec ζChar(K)).1.meromorphicOn
  have hg := (analyticOnNhd_univ_iff_differentiable.mpr hG).meromorphicOn.mul ((finiteHeckeL_exists_continuation ζChar(ℚ)).choose_spec.1.meromorphicOn.div
    (finiteHeckeL_exists_continuation ζChar(K)).choose_spec.1.meromorphicOn)
  have hEq := (hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)).trans (meromorphicContinuation_eventuallyEq hm hg he s)
  have hlocal := (analyticOnNhd_univ_iff_differentiable.mpr hG s (mem_univ _)).mul (hQ.div hK hne)
  exact (((meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hlocal.meromorphicNFAt).mp hEq).eq_of_nhds

/-- The Euler products at real part two bound both the finite Dedekind zeta function and its reciprocal
on the closed right half-plane. -/
private theorem cubicZeroCount_eulerBound (E : Type) [Field E] [NumberField E] (s : ℂ) (hs : 2 ≤ s.re) :
    ‖dedekindZeta E s‖ ≤ ‖dedekindZeta E 2‖ ∧ ‖(dedekindZeta E s)⁻¹‖ ≤ ‖dedekindZeta E 2‖ := by
  have hs' : 1 < s.re := by linarith
  have hp := dedekindZeta_hasProd E hs'
  have h₂ := dedekindZeta_hasProd E (s := 2) (by norm_num)
  have hn : dedekindZeta E s ≠ 0 :=
    by rw [← finiteHeckeL_one_eq_dedekindZeta (K := E) ⟨s, hs'⟩]; exact finiteHeckeL_ne_zero_of_one_lt_re _ _
  have hlocal (v : HeightOneSpectrum (𝓞 E)) :
      let q := (v.asIdeal.absNorm : ℂ)
      let t := q ^ (-s)
      ‖(1 - t)⁻¹‖ ≤ ‖(1 - q ^ (-(2 : ℂ)))⁻¹‖ ∧ ‖((1 - t)⁻¹)⁻¹‖ ≤ ‖(1 - q ^ (-(2 : ℂ)))⁻¹‖ := by
    intro q t
    let x := (v.asIdeal.absNorm : ℝ)
    have hx : 1 < x := by dsimp [x]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    let b := x ^ (-(2 : ℝ))
    have hb : 0 ≤ b := Real.rpow_nonneg (by linarith) _
    have hb' : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
    have ht : ‖t‖ ≤ b := by
      change ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-(2 : ℝ))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    have eq : q ^ (-(2 : ℂ)) = (b : ℂ) := by
      change (x : ℂ) ^ (-(2 : ℂ)) = ((x ^ (-(2 : ℝ)) : ℝ) : ℂ)
      simpa only [Complex.ofReal_neg, Complex.ofReal_ofNat] using (Complex.ofReal_cpow (by linarith : 0 ≤ x) (-(2 : ℝ))).symm
    have hbase : ‖(1 - q ^ (-(2 : ℂ)))⁻¹‖ = (1 - b)⁻¹ := by
      rw [eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hb')]
    rw [hbase, inv_inv]
    have hlow : 1 - b ≤ ‖1 - t‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) t
      simp only [norm_one] at hh
      linarith
    have hupper : ‖1 - t‖ ≤ 1 + b := (norm_sub_le _ _).trans (by simp; exact ht)
    constructor
    · rw [norm_inv]
      exact inv_anti₀ (by linarith) hlow
    · rw [← one_div, le_div_iff₀ (by linarith : 0 < 1 - b)]
      nlinarith [mul_le_mul_of_nonneg_left hupper (sub_nonneg.mpr hb'.le), sq_nonneg b]
  constructor
  · exact le_of_tendsto_of_tendsto hp.norm h₂.norm (Eventually.of_forall fun T ↦ by
      simp only [norm_prod]; exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ (hlocal v).1))
  · exact le_of_tendsto_of_tendsto (hp.inv₀ hn).norm h₂.norm (Eventually.of_forall fun T ↦ by
      simp only [norm_prod]; exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ (hlocal v).2))

/-- The finite continuation is regular away from the possible completed poles. -/
private theorem cubicZeroCount_finiteRegular (E : Type) [Field E] [NumberField E] {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    AnalyticAt ℂ finiteζ(E) s := by
  have hf := (finiteHeckeL_exists_continuation ζChar(E)).choose_spec
  have hL := continuedCompletedHeckeL_spec ζChar(E)
  let g (w : ℂ) := (heckeGammaFactor ζChar(E) w)⁻¹
  have hg : Differentiable ℂ g := differentiable_inv_heckeGammaFactor _
  have hg' := analyticOnNhd_univ_iff_differentiable.mpr hg
  have he := meromorphicContinuation_eventuallyEq hf.1.meromorphicOn (hL.1.meromorphicOn.mul hg'.meromorphicOn)
    (fun z hz ↦ by
      rw [hf.2 ⟨z, hz⟩, Pi.mul_apply, hL.2 ⟨z, hz⟩]
      change finiteHeckeL _ _ = (heckeGammaFactor _ _ * finiteHeckeL _ _) * (heckeGammaFactor _ _)⁻¹
      rw [mul_right_comm, mul_inv_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos _ (by linarith)), one_mul]) s
  have hlocal := (completedHeckeL_one_analyticOnNhd _ hL.1 hL.2 s (by simp [h₀, h₁])).mul (hg' s (mem_univ _))
  exact (analyticAt_congr (((hf.1 (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hlocal.meromorphicNFAt).mp he)).mpr hlocal

/-- The normalized meromorphic quotient agrees with ordinary division wherever the denominator is regular
and nonzero. -/
private theorem cubicZeroCount_quotientValue (K : Type) [Field K] [NumberField K] {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1)
    (hne : completedζ(K) s ≠ 0) : ζRatio(K) s = completedζ(ℚ) s / completedζ(K) s := by
  have hQ := continuedCompletedHeckeL_spec ζChar(ℚ)
  have hK := continuedCompletedHeckeL_spec ζChar(K)
  have h := toMeromorphicNFOn_eq_toMeromorphicNFAt (hQ.1.meromorphicOn.div hK.1.meromorphicOn) (mem_univ s)
  have he : s ∈ ({0, 1}ᶜ : Set ℂ) := by simp [h₀, h₁]
  exact h.trans (congrFun (toMeromorphicNFAt_eq_self.mpr
    ((completedHeckeL_one_analyticOnNhd _ hQ.1 hQ.2 s he).div (completedHeckeL_one_analyticOnNhd _ hK.1 hK.2 s he) hne).meromorphicNFAt) s)

/-- Nonvanishing of the completed function on the Euler half-plane. -/
private theorem cubicZeroCount_eulerNonzero (E : Type) [Field E] [NumberField E] {s : ℂ} (hs : 1 < s.re) :
    completedζ(E) s ≠ 0 := by
  rw [(continuedCompletedHeckeL_spec ζChar(E)).2 ⟨s, hs⟩]
  exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos _ (by linarith)) (finiteHeckeL_ne_zero_of_one_lt_re _ _)

/-- Reflection of the completed quotient costs an exponential in the real part, uniformly in the height. -/
private theorem cubicZeroCount_quotientReflection (K : Type) [Field K] [NumberField K] :
    ∃ A > 0, ∃ b : ℝ, ∀ s : ℂ, 1 < s.re →
      ‖ζRatio(K) (1 - s)‖ = A * Real.exp (b * (s.re - 1 / 2)) * ‖ζRatio(K) s‖ := by
  have fe (E : Type) [Field E] [NumberField E] := continuedCompletedHeckeL_spec ζChar(E)
  obtain ⟨cQ, hQ, eQ⟩ := completedHeckeL_functionalEquation_conductorScale ζChar(ℚ) _ _ (fe ℚ).1 (fe ℚ).2 (fe ℚ).1 (by simpa using (fe ℚ).2)
  obtain ⟨cK, hK, eK⟩ := completedHeckeL_functionalEquation_conductorScale ζChar(K) _ _ (fe K).1 (fe K).2 (fe K).1 (by simpa using (fe K).2)
  refine ⟨‖cQ‖ / ‖cK‖, div_pos (norm_pos_iff.mpr hQ) (norm_pos_iff.mpr hK),
    heckeLogDiscriminantConductor ζChar(ℚ) - heckeLogDiscriminantConductor ζChar(K), fun s hs ↦ ?_⟩
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hn := cubicZeroCount_eulerNonzero K hs
  rw [cubicZeroCount_quotientValue K (sub_ne_zero.mpr h1.symm) (by simpa using h0) (by rw [eK]; exact mul_ne_zero (mul_ne_zero hK (Complex.exp_ne_zero _)) hn),
    cubicZeroCount_quotientValue K h0 h1 hn, eQ, eK]
  simp only [norm_div, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  rw [sub_mul, Real.exp_sub]
  ring

/-- The gamma recurrence gives uniform factorial decay on the sequence of right edges. -/
private theorem cubicZeroCount_gammaRight (w : ℝ) (hw : 0 ≤ w) :
    ∃ D > 0, ∃ B : ℝ, ∀ (n : ℕ) (s : ℂ), s.re = 2 * ((n : ℝ) + 1) + 1 / 2 →
      ‖(Gammaℝ (s + w))⁻¹‖ ≤ D ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |s.im|) := by
  obtain ⟨A, hA, B, h⟩ := cubicZeroCount_gammaStrip (5 / 2 + w) (5 / 2 + w)
  let D := max A (2 * Real.pi)
  have hD : 0 < D := hA.trans_le (le_max_left ..)
  refine ⟨D, hD, B, fun n s hs ↦ ?_⟩
  let u := s + (w : ℂ) - 2 * n
  have hu : u.re = 5 / 2 + w := by dsimp [u]; simp [Complex.mul_re, hs]; ring
  have hi : u.im = s.im := by simp [u, Complex.mul_im]
  have he := cubicZeroCount_gammaRecurrence u (by linarith) n
  have hz : u + 2 * (n : ℂ) = s + w := sub_add_cancel _ _
  rw [hz] at he
  have h₁ := h u (by rw [hu]; exact ⟨le_rfl, le_rfl⟩)
  rw [hi] at h₁
  have h₂ : (2 * Real.pi) ^ n * A ≤ D ^ (n + 1) := by
    rw [pow_succ]; gcongr
    · exact le_max_right ..
    · exact le_max_left ..
  have hden : 0 < (n.factorial : ℝ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden, mul_comm]
  calc _ ≤ (2 * Real.pi) ^ n * ‖(Gammaℝ u)⁻¹‖ := he
       _ ≤ (2 * Real.pi) ^ n * (A * Real.exp (B * |s.im|)) := by gcongr
       _ ≤ _ := by rw [← mul_assoc]; gcongr

/-- On the right edge the Euler factors stay bounded while both reciprocal gamma factors decay. -/
private theorem cubicZeroCount_rightEdge (K : Type) [Field K] [NumberField K] (c w : ℝ) (hc : 0 < c) (hw : 0 ≤ w)
    (he : ∀ s : ℂ, 1 < s.re →
      completedζ(ℚ) s / completedζ(K) s = c * (Gammaℝ s)⁻¹ * (Gammaℝ (s + (w : ℂ)))⁻¹ * (finiteζ(ℚ) s / finiteζ(K) s)) :
    ∃ D > 0, ∃ B : ℝ, ∀ (n : ℕ) (s : ℂ), s.re = 2 * ((n : ℝ) + 1) + 1 / 2 →
      ‖ζRatio(K) s‖ ≤ D ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |s.im|) := by
  obtain ⟨D, hD, B, g⟩ := cubicZeroCount_gammaRight 0 le_rfl
  obtain ⟨D', hD', B', g'⟩ := cubicZeroCount_gammaRight w hw
  let C := 1 + c * ‖dedekindZeta ℚ 2‖*‖dedekindZeta K 2‖
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C * (D * D'), by positivity, B + B', fun n s hs ↦ ?_⟩
  have hx : 2 ≤ s.re := by rw [hs]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have h : 1 < s.re := by linarith
  have hn (E : Type) [Field E] [NumberField E] : finiteζ(E) s = dedekindZeta E s :=
    ((finiteHeckeL_exists_continuation ζChar(E)).choose_spec.2 ⟨s, h⟩).trans (finiteHeckeL_one_eq_dedekindZeta _)
  have g₁ := g n s hs
  simp only [ofReal_zero, add_zero] at g₁
  have g₂ : ‖(Gammaℝ (s + w))⁻¹‖ ≤ D'^(n + 1) * Real.exp (B'*|s.im|) := by
    apply (g' n s hs).trans
    gcongr
    apply div_le_self (by positivity)
    exact_mod_cast Nat.factorial_pos n
  have hp : c * ‖dedekindZeta ℚ 2‖*‖dedekindZeta K 2‖ ≤ C ^ (n + 1) :=
    (le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ hC (Nat.succ_ne_zero n))
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at h
  have hs₁ : s ≠ 1 := by rintro rfl; norm_num at h
  rw [cubicZeroCount_quotientValue K hs₀ hs₁ (cubicZeroCount_eulerNonzero K h), he s h, hn ℚ, hn K,
    div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ c * (D ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |s.im|)) *
      (D'^(n + 1) * Real.exp (B'*|s.im|)) * (‖dedekindZeta ℚ 2‖*‖dedekindZeta K 2‖) := by
        gcongr
        · exact (cubicZeroCount_eulerBound ℚ s hx).1
        · exact (cubicZeroCount_eulerBound K s hx).2
    _ = (c * ‖dedekindZeta ℚ 2‖*‖dedekindZeta K 2‖) *
        (D ^ (n + 1) * D'^(n + 1) / (n.factorial : ℝ) * Real.exp ((B + B') * |s.im|)) := by rw [add_mul, Real.exp_add]; ring
    _ ≤ _ := by rw [mul_pow, mul_pow]; grw [hp]; ring_nf; rfl

/-- Reflect the right-edge bound to the left edge of the same centered box. -/
private theorem cubicZeroCount_verticalEdges (K : Type) [Field K] [NumberField K]
    {D B : ℝ} (hD : 0 < D)
    (hr : ∀ (n : ℕ) (s : ℂ), s.re = 2 * ((n : ℝ) + 1) + 1 / 2 →
      ‖ζRatio(K) s‖ ≤ D ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |s.im|)) :
    ∃ D' > 0, ∀ (n : ℕ) (z : ℂ), |z.re| = 2 * (n + 1 : ℝ) →
      ‖ζRatio(K) (z + 1 / 2)‖ ≤ D'^(n + 1) / (n.factorial : ℝ) * Real.exp (B * |z.im|) := by
  obtain ⟨A, hA, b, hf⟩ := cubicZeroCount_quotientReflection K
  let C := (max 1 A) * Real.exp (2 * |b|)
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le (le_max_left ..) (Real.one_le_exp (by positivity))
  refine ⟨C * D, mul_pos (zero_lt_one.trans_le hC) hD, fun n z hz ↦ ?_⟩
  have hh : (0 : ℝ) ≤ 2 * (n + 1 : ℝ) := by positivity
  rcases (abs_eq hh).mp hz with hp | hm
  · have h := hr n (z + 1 / 2) (by simp [hp])
    simp only [add_im, div_ofNat_im, one_im, zero_div, add_zero] at h
    apply h.trans; gcongr; exact le_mul_of_one_le_left hD.le hC
  · let s := -z + 1 / 2
    have hs : s.re = 2 * (n + 1 : ℝ) + 1 / 2 := by simp [s, hm]
    have hs' : 1 < s.re := by rw [hs]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hi : |s.im| = |z.im| := by simp [s]
    have eq : z + 1 / 2 = 1 - s := by dsimp [s]; ring
    have hA₁ : A ≤ (max 1 A) ^ (n + 1) := (le_max_right ..).trans (le_self_pow₀ (le_max_left ..) (Nat.succ_ne_zero n))
    have hp : A * Real.exp (b * (s.re - 1 / 2)) ≤ C ^ (n + 1) := by
      dsimp [C]; rw [mul_pow, ← Real.exp_nat_mul]
      apply mul_le_mul hA₁ _ (Real.exp_pos _).le (by positivity)
      apply Real.exp_le_exp.mpr
      rw [hs]; push_cast; nlinarith [mul_le_mul_of_nonneg_right (le_abs_self b) hh]
    rw [eq, hf s hs']
    calc
      _ ≤ C ^ (n + 1) * (D ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |s.im|)) := by gcongr; exact hr n s hs
      _ = _ := by rw [hi, mul_pow]; ring

/-- Choose horizontal edges using the polynomial reciprocal bound for the finite cubic zeta function.
Their heights may depend on the width of the box. -/
private theorem cubicZeroCount_horizontalEdges (K : Type) [Field K] [NumberField K] (c w : ℝ) (hc : 0 < c)
    (he : ∀ s : ℂ, 1 < s.re →
      completedζ(ℚ) s / completedζ(K) s = c * (Gammaℝ s)⁻¹ * (Gammaℝ (s + (w : ℂ)))⁻¹ * (finiteζ(ℚ) s / finiteζ(K) s))
    (R : ℝ) (hR : 0 < R) :
    ∃ A > 0, ∃ b : ℝ, ∀ S > (0 : ℝ), ∃ lo hi : ℝ, lo < -S ∧ S < hi ∧
      ∀ z : ℂ, |z.re| ≤ R → z.im = lo ∨ z.im = hi → ‖ζRatio(K) (z + 1 / 2)‖ ≤ A * Real.exp (b * |z.im|) := by
  let a : ℝ := 1 / 2 - R
  let d : ℝ := 1 / 2 + R
  have had : a < d := by dsimp [a, d]; linarith
  obtain ⟨A, hA, B, hΓ⟩ := cubicZeroCount_gammaStrip a d
  obtain ⟨A', hA', B', hΓ'⟩ := cubicZeroCount_gammaStrip (a + w) (d + w)
  have hQ := (finiteHeckeL_exists_continuation ζChar(ℚ)).choose_spec
  obtain ⟨M, hM, hO⟩ := finiteHeckeL_continuation_isBigO_rpow ζChar(ℚ) _ hQ.1 hQ.2 a d had
  obtain ⟨C, hC, hC'⟩ := Asymptotics.isBigO_iff'.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hC'
  obtain ⟨T₀, hT₀⟩ := hC'
  obtain ⟨T, D, m, hD, hi, hl, hbound⟩ := introTrace_finiteL_inv_horizontal_growth ζChar(K) a d had
  refine ⟨c * A * A'*(C * D), by positivity, B + B'+M + m, fun S hS ↦ ?_⟩
  let Y := max 1 (max S T₀)
  obtain ⟨k, hk⟩ := (hl.eventually (eventually_lt_atBot (-Y))).exists
  obtain ⟨j, hj⟩ := (hi.eventually (eventually_gt_atTop Y)).exists
  have hSY : S ≤ Y := le_trans (le_max_left ..) (le_max_right ..)
  have hTY : T₀ ≤ Y := le_trans (le_max_right ..) (le_max_right ..)
  have hY : 1 ≤ Y := le_max_left ..
  refine ⟨T k, T j, by linarith, by linarith, fun z hx hyv ↦ ?_⟩
  let s := z + 1 / 2
  have hs : s.re ∈ Icc a d := by
    dsimp [s, a, d]
    simp only [div_ofNat_re, one_re]
    constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have him : s.im = z.im := by simp [s]
  have hy : Y ≤ |z.im| := by
    rcases hyv with h | h
    · rw [h, abs_of_neg (by linarith : T k < 0)]; linarith
    · rw [h, abs_of_pos (by linarith : 0 < T j)]; linarith
  have hden : meromorphicOrderAt finiteζ(K) s = 0 ∧ ‖(finiteζ(K) s)⁻¹‖ ≤ D * (1 + |z.im|) ^ m := by
    rcases hyv with h|h
    · simpa [← h, ← him] using hbound k s.re hs
    · simpa [← h, ← him] using hbound j s.re hs
  have hf := (finiteHeckeL_exists_continuation ζChar(K)).choose_spec.1 (mem_univ s)
  have hAf := hf.meromorphicOrderAt_nonneg_iff_analyticAt.mp hden.1.ge
  have hn := hf.meromorphicOrderAt_eq_zero_iff.mp hden.1
  have hnon (x : ℂ) (hx : x.im = 0) : s ≠ x := by intro h; rw [← him, h, hx, abs_zero] at hy; linarith
  have hZ := cubicZeroCount_finiteQuotient K c w he s (cubicZeroCount_finiteRegular ℚ (hnon 0 rfl) (hnon 1 rfl)) hAf hn
  have hq := hT₀ |s.im| (him ▸ hTY.trans hy) s rfl hs
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), him] at hq
  have hqp : |z.im| ^ M ≤ Real.exp (M * |z.im|) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < |z.im|), Real.exp_le_exp, mul_comm]
    gcongr; exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hkp : (1 + |z.im|) ^ m ≤ Real.exp ((m : ℝ) * |z.im|) := by
    rw [Real.exp_nat_mul]; gcongr; linarith [Real.add_one_le_exp |z.im|]
  have hshift : (s + (w : ℂ)).re ∈ Icc (a + w) (d + w) := by simpa using hs
  have hga := hΓ s hs
  have hgb := hΓ' (s + (w : ℂ)) hshift
  simp only [add_im, ofReal_im, add_zero, him] at hga hgb
  change ‖ζRatio(K) s‖ ≤ _
  rw [hZ, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ c * (A * Real.exp (B * |z.im|)) * (A' * Real.exp (B'*|z.im|)) *
        ((C * Real.exp (M * |z.im|)) * (D * Real.exp ((m : ℝ) * |z.im|))) := by
      gcongr
      · exact hq.trans (by gcongr)
      · exact hden.2.trans (by gcongr)
    _ = _ := by simp only [add_mul, Real.exp_add]; ring

/-- Finitely many possible poles can simultaneously be removed by a polynomial.
The exponents come from the defining property of meromorphicity at those points. -/
private theorem cubicZeroCount_clearFinitePoles (K : Type) [Field K] [NumberField K] (T : Finset ℂ)
    (hT : ∀ z ∉ T, 0 < z.re → z.re < 1 → order(ζChar(K), z) ≤ order(ζChar(ℚ), z)) :
    ∃ m : ℂ → ℕ, Differentiable ℂ (fun z ↦ (∏ a ∈ T, (z - a) ^ m a) * ζRatio(K) z) := by
  classical
  have H := meromorphicNFOn_toMeromorphicNFOn (completedζ(ℚ) / completedζ(K)) univ
  have hmer (z : ℂ) := (H (mem_univ z)).meromorphicAt
  let m (z : ℂ) := (hmer z).choose
  refine ⟨m, fun z ↦ AnalyticAt.differentiableAt ?_⟩
  by_cases hz : z ∈ T
  · have hc : AnalyticAt ℂ (fun w ↦ (w - z) ^ m z * ζRatio(K) w) z := (hmer z).choose_spec
    have hd : AnalyticAt ℂ (fun w : ℂ ↦ ∏ a ∈ T.erase z, (w - a) ^ m a) z := by fun_prop
    have he : (fun w ↦ (∏ a ∈ T, (w - a) ^ m a) * ζRatio(K) w) =
        (fun w ↦ (∏ a ∈ T.erase z, (w - a) ^ m a) * ((w - z) ^ m z * ζRatio(K) w)) := by
      funext w
      rw [← Finset.mul_prod_erase _ _ hz]
      ring
    rw [he]
    exact hd.mul hc
  · apply AnalyticAt.mul (by fun_prop)
    apply (H (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    have hQ := continuedCompletedHeckeL_spec ζChar(ℚ)
    have hK := continuedCompletedHeckeL_spec ζChar(K)
    rw [meromorphicOrderAt_toMeromorphicNFOn (hQ.1.meromorphicOn.div hK.1.meromorphicOn) (mem_univ _),
      meromorphicOrderAt_div (hQ.1.meromorphicOn z (mem_univ _)) (hK.1.meromorphicOn z (mem_univ _))]
    by_cases h₀ : z = 0
    · subst z; rw [(cubicZeroCount_poles ℚ).1, (cubicZeroCount_poles K).1]; decide
    by_cases h₁ : z = 1
    · subst z; rw [(cubicZeroCount_poles ℚ).2, (cubicZeroCount_poles K).2]; decide
    by_cases h : 0 < z.re ∧ z.re < 1
    · rw [spectralLineJet_memLp_false_stripOrder ℚ z h.1 h.2, spectralLineJet_memLp_false_stripOrder K z h.1 h.2]
      exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (Int.ofNat_le.mpr (hT z hz h.1 h.2)))
    · have hx : z.re ≤ 0 ∨ 1 ≤ z.re := by grind
      rw [cubicZeroCount_exteriorOrder ℚ z hx h₀ h₁, cubicZeroCount_exteriorOrder K z hx h₀ h₁]
      decide

/-- A finite product of shifted linear factors grows at most exponentially in
the width and height of the contour. -/
private theorem cubicZeroCount_polynomialBound (T : Finset ℂ) (m : ℂ → ℕ) (c : ℂ) :
    ∃ A : ℝ, ∃ d ≥ (0 : ℝ), ∀ z : ℂ, ‖∏ a ∈ T, (z + c - a) ^ m a‖ ≤
      Real.exp (A + d * (|z.re| + |z.im|)) := by
  let H (a : ℂ) := (m a : ℝ) * ‖c - a‖
  let w (a : ℂ) := (m a : ℝ)
  refine ⟨∑ a ∈ T, H a, ∑ a ∈ T, w a, Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _), fun z ↦ ?_⟩
  let r := |z.re| + |z.im|
  have hf (a : ℂ) : ‖z + c - a‖ ≤ Real.exp (‖c - a‖ + r) := by
    have hn : ‖z + c - a‖ ≤ ‖c - a‖ + r := by
      rw [add_sub_assoc, add_comm]
      exact (norm_add_le _ _).trans (add_le_add_right (Complex.norm_le_abs_re_add_abs_im z) _)
    linarith [Real.add_one_le_exp (‖c - a‖ + r)]
  calc
    ‖∏ a ∈ T, (z + c - a) ^ m a‖ ≤ ∏ a ∈ T, ‖z + c - a‖ ^ m a := by
      simp
    _ ≤ ∏ a ∈ T, Real.exp (‖c - a‖ + r) ^ m a := by
      gcongr with a ha
      exact hf a
    _ = Real.exp (∑ a ∈ T, H a + (∑ a ∈ T, w a) * r) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro a _
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [H, w]
      ring

/-- For every cubic number field, its completed Dedekind zeta function vanishes
to higher order than the rational one at infinitely many distinct points in the
open strip. A finite exceptional divisor could be removed by a polynomial,
whose growth preserves the factorial estimates on the rectangle edges. -/
theorem cubicDedekindZeta_excessOrders_infinite (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ order(ζChar(ℚ), z) < order(ζChar(K), z)}.Infinite := by
  classical
  intro hfin
  let T := hfin.toFinset
  have hT (z : ℂ) : z ∈ T ↔ 0 < z.re ∧ z.re < 1 ∧ order(ζChar(ℚ), z) < order(ζChar(K), z) :=
    hfin.mem_toFinset
  obtain ⟨m, hm⟩ := cubicZeroCount_clearFinitePoles K T (fun z hz h₀ h₁ ↦
    le_of_not_gt (fun h ↦ hz ((hT z).mpr ⟨h₀, h₁, h⟩)))
  let P (s : ℂ) := ∏ a ∈ T, (s - a) ^ m a
  let f (z : ℂ) := P (z + 1 / 2) * ζRatio(K) (z + 1 / 2)
  have hf : Differentiable ℂ f := hm.comp (differentiable_id.add_const _)
  obtain ⟨A, d, hd, hP⟩ := cubicZeroCount_polynomialBound T m (1 / 2)
  obtain ⟨c, w, hc, hw, _, he⟩ := cubicZeroCount_eulerFactors K hdeg
  obtain ⟨D, hD, B, hr⟩ := cubicZeroCount_rightEdge K c w hc hw he
  obtain ⟨J, hJ, hv⟩ := cubicZeroCount_verticalEdges K hD hr
  let C := max 1 (Real.exp A)
  let U := C * Real.exp (2 * d) * J
  have hC : 1 ≤ C := le_max_left _ _
  have hU : 0 < U := mul_pos (mul_pos (zero_lt_one.trans_le hC) (Real.exp_pos _)) hJ
  have vert (n : ℕ) (z : ℂ) (hz : |z.re| = 2 * (n + 1 : ℝ)) :
      ‖f z‖ ≤ U ^ (n + 1) / (n.factorial : ℝ) * Real.exp ((d + B) * |z.im|) := by
    have ha : Real.exp A ≤ C ^ (n + 1) :=
      (le_max_right 1 (Real.exp A)).trans (le_self_pow₀ hC (Nat.succ_ne_zero n))
    have hstep : Real.exp (A + d * (|z.re| + |z.im|)) =
        Real.exp A * Real.exp (2 * d) ^ (n + 1) * Real.exp (d * |z.im|) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, hz]
      congr 1
      push_cast
      ring
    have hp := hP z
    change ‖P (z + 1 / 2)‖ ≤ _ at hp
    rw [hstep] at hp
    calc
      ‖f z‖ = ‖P (z + 1 / 2)‖ * ‖ζRatio(K) (z + 1 / 2)‖ := norm_mul _ _
      _ ≤ (C ^ (n + 1) * Real.exp (2 * d) ^ (n + 1) * Real.exp (d * |z.im|)) *
          (J ^ (n + 1) / (n.factorial : ℝ) * Real.exp (B * |z.im|)) :=
        mul_le_mul (hp.trans (by gcongr)) (hv n z hz) (norm_nonneg _) (by positivity)
      _ = _ := by
        dsimp [U]
        rw [mul_pow, mul_pow, add_mul, Real.exp_add]
        ring
  have hor (n : ℕ) : ∃ a > 0, ∃ b : ℝ, ∀ S > (0 : ℝ), ∃ lo hi : ℝ,
      lo < -S ∧ S < hi ∧ ∀ z : ℂ, |z.re| ≤ 2 * (n + 1 : ℝ) → z.im = lo ∨ z.im = hi →
        ‖f z‖ ≤ a * Real.exp (b * |z.im|) := by
    let R := 2 * (n + 1 : ℝ)
    obtain ⟨a, ha, b, hh⟩ := cubicZeroCount_horizontalEdges K c w hc he R
      (by dsimp [R]; positivity)
    refine ⟨Real.exp (A + d * R) * a, mul_pos (Real.exp_pos _) ha, d + b, fun S hS ↦ ?_⟩
    obtain ⟨lo, hi, hlo, hhi, hstrip⟩ := hh S hS
    refine ⟨lo, hi, hlo, hhi, fun z hx hy ↦ ?_⟩
    have hp : ‖P (z + 1 / 2)‖ ≤ Real.exp (A + d * R) * Real.exp (d * |z.im|) := by
      refine (hP z).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hx hd]
    calc
      ‖f z‖ = ‖P (z + 1 / 2)‖ * ‖ζRatio(K) (z + 1 / 2)‖ := norm_mul _ _
      _ ≤ (Real.exp (A + d * R) * Real.exp (d * |z.im|)) * (a * Real.exp (b * |z.im|)) :=
        mul_le_mul hp (hstrip z hx hy) (norm_nonneg _) (by positivity)
      _ = _ := by rw [add_mul, Real.exp_add (d * |z.im|) (b * |z.im|)]; ring
  have hzero := cubicZeroCount_factorialEdges f hf U (d + B) hU vert hor
  let s : ℂ := 1 + 1 / 2
  have hs : 1 < s.re := by norm_num [s]
  change P s * ζRatio(K) s = 0 at hzero
  have hn : P s ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun h ↦ ((hT a).mp ha).2.1.not_ge (h ▸ hs.le)))
  apply (mul_ne_zero hn ?_) hzero
  rw [cubicZeroCount_quotientValue K (by norm_num [s]) (by norm_num [s]) (cubicZeroCount_eulerNonzero K hs)]
  exact div_ne_zero (cubicZeroCount_eulerNonzero ℚ hs) (cubicZeroCount_eulerNonzero K hs)

/-- On some finite subset of the open critical strip, the zero count with multiplicity
for ℚ(∛2) exceeds the rational zero count. The Dedekind zero-count asymptotic has
leading coefficient proportional to the degree, which is three for the cubic field.
Alternatively the critical-line sign change of the cubic ξ-function between heights
zero and three gives a singleton, since rational ζ is zero-free there. -/
private theorem spectralLineJet_memLp_false_cubicZeroCount
    (K : Type) [Field K] [NumberField K] (b : PowerBasis ℚ K)
    (_hb : b.gen ^ 3 = 2) (_hd : b.dim = 3) :
    ∃ S : Finset ℂ, (∀ z ∈ S, 0 < z.re ∧ z.re < 1) ∧
      (∑ z ∈ S, order((1 : PontryaginDual C𝔽(ℚ)), z)) <
        ∑ z ∈ S, order((1 : PontryaginDual C𝔽(K)), z) := by
  classical
  obtain ⟨z, h₀, h₁, h⟩ := (cubicDedekindZeta_excessOrders_infinite K (b.finrank.trans _hd)).nonempty
  exact ⟨{z}, by simpa using And.intro h₀ h₁, by simpa using h⟩

/-- A cubic subfield of the splitting field of X³ − 2 detects double zeros:
an excess over the rational zero order forces order at least two upstairs. -/
private theorem cubicZeroCount_splittingField_comparison :
    let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
    letI : NumberField L := ⟨⟩
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (b : PowerBasis ℚ K),
      b.gen ^ 3 = 2 ∧ b.dim = 3 ∧ ∀ z : ℂ, 0 < z.re → z.re < 1 →
        order(ζChar(ℚ), z) < order(ζChar(K), z) → 1 < order(ζChar(L), z) := by
  classical
  let P : Polynomial ℚ := Polynomial.X ^ 3 - Polynomial.C 2
  let Q : Polynomial ℚ := Polynomial.X ^ 2 + Polynomial.C 3
  have : Fact (Irreducible P) := by
    constructor
    apply irreducible_X_pow_sub_C_of_prime (by decide : Nat.Prime 3)
    intro q hq
    have h := congrArg (padicValRat 2) hq
    rw [padicValRat.pow, show padicValRat 2 2 = 1 from padicValRat.self (by decide : 1 < 2)] at h
    norm_num at h
    omega
  have hirr : Irreducible P := (inferInstance : Fact (Irreducible P)).out
  let K := AdjoinRoot P
  let L := P.SplittingField
  let k := Q.SplittingField
  have : IsGalois ℚ L := IsGalois.of_separable_splitting_field hirr.separable
  have : NumberField L := ⟨⟩
  have : NumberField k := ⟨⟩
  let b := AdjoinRoot.powerBasis (Polynomial.X_pow_sub_C_ne_zero (by decide : 0 < 3) (2 : ℚ))
  have hb : b.gen ^ 3 = 2 := by
    change (AdjoinRoot.root P) ^ 3 = 2
    have he := AdjoinRoot.eval₂_root P
    simpa only [P, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.eval₂_ofNat, map_ofNat, sub_eq_zero] using he
  have hd : b.dim = 3 := by rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_sub_C]
  have hG := spectralLineJet_memLp_false_cubicGalois P rfl hirr
  obtain ⟨ιK, ιk, hk⟩ := spectralLineJet_memLp_false_subfields P rfl hirr
  have hprimes := spectralLineJet_memLp_false_primeCounts L k K hG ιk hk ιK (b.finrank.trans hd)
  refine ⟨K, inferInstance, inferInstance, b, hb, hd, fun z h₀ h₁ hx ↦ ?_⟩
  have hrel := spectralLineJet_memLp_false_orderRelation L k K
    (spectralLineJet_memLp_false_zetaRelation L k K hprimes) z h₀ h₁
  omega


/-- The fixed splitting field of X³−2 has infinitely many distinct multiple
zeros in the open strip, for its trivial Hecke character. -/
theorem cubicSplittingField_completedDedekindZeta_multipleZeros_infinite :
    let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
    letI : NumberField L := ⟨⟩
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < order(ζChar(L), z)}.Infinite := by
  let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
  letI : NumberField L := ⟨⟩
  obtain ⟨K, _, _, b, _, hd, ht⟩ := cubicZeroCount_splittingField_comparison
  change {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < order(ζChar(L), z)}.Infinite
  apply (cubicDedekindZeta_excessOrders_infinite K (b.finrank.trans hd)).mono
  rintro z ⟨h₀, h₁, hz⟩
  exact ⟨h₀, h₁, ht z h₀ h₁ hz⟩

/-- Reflection and local finiteness of the divisor turn infinitely many
multiple zeros in the open strip into unbounded positive ordinates. -/
private theorem cubicZeroCount_unbounded_of_infinite (E : Type) [Field E] [NumberField E]
    (hi : {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < order(ζChar(E), z)}.Infinite) (B : ℝ) :
    ∃ z : ℂ, B < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 < order(ζChar(E), z) := by
  classical
  by_contra! h
  let S := {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < order(ζChar(E), z)}
  have hb : ∀ z ∈ S, z.im ≤ B := by
    rintro z ⟨h₀, h₁, hm⟩
    by_contra! hn
    exact (h z hn h₀ h₁).not_gt hm
  have hsym : ∀ z ∈ S, 1 - z ∈ S := by
    rintro z ⟨h₀, h₁, hm⟩
    refine ⟨by simp; linarith, by simp; exact h₀,?_⟩
    rw [cubicZeroCount_reflectedOrder]
    exact hm
  let D := Metric.closedBall (0 : ℂ) (1 + |B|)
  have hD : IsCompact D := isCompact_closedBall _ _
  have hSD (z : ℂ) (hz : z ∈ S) : z ∈ D := by
    have hpos := hb z hz
    have hneg := hb (1 - z) (hsym z hz)
    simp at hneg
    have hi : |z.im| ≤ |B| := abs_le.mpr ⟨by linarith [le_abs_self B],by linarith [le_abs_self B]⟩
    have hx : 0 < z.re ∧ z.re < 1 := ⟨hz.1, hz.2.1⟩
    change dist z 0 ≤ 1 + |B|
    rw [dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add
      (by rw [abs_of_pos hx.1]; exact hx.2.le) hi)
  have hm : MeromorphicOn completedζ(E) D := fun z _ ↦ (continuedCompletedHeckeL_spec ζChar(E)).1.meromorphicOn z (mem_univ z)
  apply hi
  apply ((MeromorphicOn.divisor completedζ(E) D).finiteSupport hD).subset
  intro z hz
  change MeromorphicOn.divisor completedζ(E) D z ≠ 0
  rw [hm.divisor_apply (hSD z hz)]
  have hp : 1 < order(ζChar(E), z) := hz.2.2
  intro he
  rw [he] at hp
  simp at hp

/-- Positive ordinates of genuine multiple zeros of the fixed completed
Dedekind zeta function are unbounded. -/
theorem cubicSplittingField_completedDedekindZeta_multipleZeros_unbounded (B : ℝ) :
    let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
    letI : NumberField L := ⟨⟩
    ∃ z : ℂ, B < z.im ∧ 0 < z.re ∧ z.re < 1 ∧ 1 < order(ζChar(L), z) := by
  let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
  letI : NumberField L := ⟨⟩
  exact cubicZeroCount_unbounded_of_infinite L cubicSplittingField_completedDedekindZeta_multipleZeros_infinite B

end CubicZeroCount

/-- Paper: Theorem 10.2.1.1, p. 440. The trivial Hecke character of some
number field has a completed L-function with a zero of multiplicity at least two
in the open critical strip. The witness is the splitting field of X³ − 2. -/
theorem exists_completedDedekindZeta_multipleZero :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (z : ℂ),
      0 < z.re ∧ z.re < 1 ∧ 1 < order((1 : PontryaginDual C𝔽(F)), z) := by
  classical
  let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
  letI : NumberField L := ⟨⟩
  obtain ⟨K, _, _, b, hb, hd, ht⟩ := cubicZeroCount_splittingField_comparison
  obtain ⟨S, hS, hlt⟩ := spectralLineJet_memLp_false_cubicZeroCount K b hb hd
  obtain ⟨z, hz, ho⟩ : ∃ z ∈ S, order((1 : PontryaginDual C𝔽(ℚ)), z) < order((1 : PontryaginDual C𝔽(K)), z) := by
    by_contra! h
    exact hlt.not_ge (Finset.sum_le_sum h)
  exact ⟨L, inferInstance, inferInstance, z,(hS z hz).1,(hS z hz).2, ht z (hS z hz).1 (hS z hz).2 ho⟩

end RiemannMasullo
