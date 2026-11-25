module

public import RiemannMasullo.ForMathlib.NumberTheory.WeilBound.NonCancellation

/-!
# Weil's bound, III: Bombieri's two counts

For `A = k[t][Y]/F` over a finite field `k` with `q` elements and `Q = q ^ (m₀ + m₁)`:

* `card_fixed_le`: the `k`-algebra maps `φ : A → M` with `φ (t), φ (y) ∈ 𝔽_Q` (the points of
  the curve over `𝔽_Q`) number at most `d (a + q₁ b) + w d²` (`q₁ = q ^ m₁`), for parameters
  `a, b` satisfying Bombieri's inequalities. With `a ≈ q₁ / d`, `b ≈ q₀ / d` this is
  `Q + O(√Q)`.
* `card_moved_le`: those with `φ (t) ∈ 𝔽_Q` but `φ (y) ∉ 𝔽_Q` also number at most
  `d (a + q₁ b) + w d²`, now for `b ≈ (d - 1) q₀ / d`, which gives `(d - 1) Q + O(√Q)`. These
  are the points `x` of the curve with `Frob x` on the off-diagonal part of `X ×_{ℙ¹} X`. Since
  all `d Q + O(1)` points with `t (x) ∈ 𝔽_Q` are fixed or moved, this upper bound is the
  **lower bound** for the fixed points. It replaces the Galois closure and the twisted
  Frobenius counts of the classical proof (Bombieri, Schmidt, Stichtenoth §5.2).

Both counts use the auxiliary function `h = ∑ f_g g ^ q₁` of Bombieri (`card_le_of_ker`), its
non-vanishing (`nonCancellation`) and the zero count (`card_algHom_apply_eq_zero_le`).
-/

@[expose] public section

open Polynomial
open scoped PowerSeries

namespace RiemannMasullo.WeilBound

section Domain

variable {k : Type*} [Field k] (L : Type*) [Field L] [Algebra k L] {F : k[X][X]} (hF : F.Monic)

include hF in
theorem ι_injective : Function.Injective (ι L F) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  set B := monoBasis hF
  set B' := monoBasis (baseChange_monic L hF)
  have hdeg := natDegree_baseChange L hF
  let e : ℕ × Fin F.natDegree → ℕ × Fin (baseChange L F).natDegree :=
    fun l => (l.1, Fin.cast hdeg.symm l.2)
  have he : Function.Injective e := by
    intro l l' hll'
    simp only [e, Prod.mk.injEq] at hll'
    exact Prod.ext hll'.1 (Fin.cast_injective _ hll'.2)
  have hsum : ∑ l ∈ (B.repr x).support, algebraMap k L (B.repr x l) • B' (e l) = 0 := by
    rw [← hx]
    conv_rhs => rw [← B.linearCombination_repr x, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ι_monoBasis L hF, algebraMap_smul]
  have hli := linearIndependent_iff'.1 (B'.linearIndependent.comp e he) _ _ hsum
  have : B.repr x = 0 := by
    ext l
    by_cases hl : l ∈ (B.repr x).support
    · exact (algebraMap k L).injective ((hli l hl).trans (map_zero _).symm)
    · simpa using hl
  simpa using congrArg B.repr.symm this

include hF in
theorem isDomain_of_baseChange [IsDomain (AdjoinRoot (baseChange L F))] :
    IsDomain (AdjoinRoot F) :=
  (ι_injective L hF).isDomain (ι L F).toRingHom

end Domain


section Count

variable {k : Type*} [Field k] [Fintype k] {L : Type*} [Field L] [Algebra k L]
  {F : k[X][X]} (hF : F.Monic) {w : ℕ}
  (hw : ∀ i < F.natDegree, (F.coeff i).natDegree ≤ (F.natDegree - i) * w)

theorem finrank_unknowns (a b : ℕ) :
    Module.finrank k (idx F w b → filt hF w a) =
      (idx F w b).card * Module.finrank k (filt hF w a) := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe]

include hw in
/-- **Bombieri's counting step.** Let `Φ` be a linear condition on the unknowns
`f : (monomials of weight ≤ b) → (weight ≤ a)` with fewer equations than unknowns. If every
`φ ∈ S` kills `h_f = ∑ f_g g ^ q₁` whenever `Φ f = 0`, then `#S ≤ d (a + q₁ b) + w d²`. -/
theorem card_le_of_ker [IsDomain (AdjoinRoot (baseChange L F))]
    (ψ : AdjoinRoot (baseChange L F) →ₐ[L] L⟦X⟧) (c : L)
    (hψ : ψ (AdjoinRoot.of _ X) = PowerSeries.C c + PowerSeries.X)
    {a b m : ℕ} (ha : F.natDegree * a + w * F.natDegree * F.natDegree < Fintype.card k ^ m)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (Φ : (idx F w b → filt hF w a) →ₗ[k] V)
    (hV : Module.finrank k V < (idx F w b).card * Module.finrank k (filt hF w a))
    {M : Type*} [Field M] [Algebra k M] (S : Set (AdjoinRoot F →ₐ[k] M))
    (hS : ∀ f ∈ LinearMap.ker Φ, ∀ φ ∈ S,
      φ (∑ g : idx F w b, (f g : AdjoinRoot F) * monoBasis hF g ^ (Fintype.card k ^ m)) = 0) :
    S.Finite ∧ S.ncard ≤
      F.natDegree * (a + Fintype.card k ^ m * b) + w * F.natDegree * F.natDegree := by
  classical
  have hdom := isDomain_of_baseChange L hF
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ)
    (by rw [finrank_unknowns]; exact hV)
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hker
  set h := ∑ g : idx F w b, (f g : AdjoinRoot F) * monoBasis hF g ^ (Fintype.card k ^ m)
  have hmem : h ∈ filt hF w (a + Fintype.card k ^ m * b) := by
    refine Submodule.sum_mem _ fun g _ => mul_mem_filt hF hw (f g).2 ?_
    exact pow_mem_filt hF hw (monoBasis_mem_filt hF (mem_idx.1 g.2)) _
  have hh0 : h ≠ 0 := by
    intro hh
    let f' : ℕ × Fin F.natDegree → AdjoinRoot F :=
      fun g => if hg : g ∈ idx F w b then (f ⟨g, hg⟩ : AdjoinRoot F) else 0
    have hf' : ∀ g ∈ idx F w b, f' g ∈ filt hF w a := by
      intro g hg; simp only [f', hg, dite_true]; exact (f ⟨g, hg⟩).2
    have hsum : ∑ g ∈ idx F w b, f' g * monoBasis hF g ^ (Fintype.card k ^ m) = 0 := by
      rw [← hh, ← Finset.sum_coe_sort (idx F w b)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [f', g.2, dite_true]
    have := nonCancellation hF hw ψ c hψ ha (idx F w b) f' hf' hsum
    apply hf0
    funext g
    have h1 := this g.1 g.2
    simp only [f', g.2, dite_true] at h1
    exact Subtype.ext h1
  obtain ⟨hfin, hcard⟩ := card_algHom_apply_eq_zero_le hF hw M hmem hh0
  have hsub : S ⊆ {φ | φ h = 0} := fun φ hφ => hS f hf φ hφ
  have hfin' : ({φ | φ h = 0} : Set (AdjoinRoot F →ₐ[k] M)).Finite := Set.toFinite _
  refine ⟨hfin'.subset hsub, ?_⟩
  calc S.ncard ≤ ({φ | φ h = 0} : Set (AdjoinRoot F →ₐ[k] M)).ncard :=
        Set.ncard_le_ncard hsub hfin'
    _ = Nat.card {φ : AdjoinRoot F →ₐ[k] M // φ h = 0} := (Nat.card_coe_set_eq _).symm
    _ ≤ _ := hcard


omit [Fintype k] in
/-- The identity behind both counts: if `φ (t) ^ Q = φ (t)` with `Q = q₀ q₁`, then
`φ(∑ f_g g ^ q₁) ^ q₀ = ∑ φ (f_g ^ q₀ t ^ j) (φ (y) ^ Q) ^ i`, where `g = t ^ j y ^ i`. -/
theorem frob_identity {M : Type*} [Field M] [Algebra k M] (φ : AdjoinRoot F →ₐ[k] M)
    {b q₀ q₁ : ℕ} (ht : φ (AdjoinRoot.of F X) ^ (q₀ * q₁) = φ (AdjoinRoot.of F X))
    (hadd : ∀ x y : AdjoinRoot F, (x + y) ^ q₀ = x ^ q₀ + y ^ q₀)
    (f : idx F w b → AdjoinRoot F) :
    φ (∑ g : idx F w b, f g * monoBasis hF g ^ q₁) ^ q₀ =
      ∑ g : idx F w b, φ (f g ^ q₀ * AdjoinRoot.of F (X ^ g.1.1)) *
        (φ (AdjoinRoot.root F) ^ (q₀ * q₁)) ^ (g.1.2 : ℕ) := by
  classical
  have hsum : ∀ s : Finset (idx F w b), (∑ g ∈ s, f g * monoBasis hF g ^ q₁) ^ q₀ =
      ∑ g ∈ s, (f g * monoBasis hF g ^ q₁) ^ q₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rcases Nat.eq_zero_or_pos q₀ with h0 | h0
      · subst h0
        have := hadd 0 0
        simpa using this
      · simp [zero_pow h0.ne']
    | insert g s hg ih => rw [Finset.sum_insert hg, Finset.sum_insert hg, hadd, ih]
  rw [← map_pow, hsum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_pow, ← pow_mul, monoBasis_apply]
  simp only [map_mul, map_pow]
  set x := φ (AdjoinRoot.of F X)
  set y := φ (AdjoinRoot.root F)
  rw [show (x ^ g.1.1 * y ^ (g.1.2 : ℕ)) ^ (q₁ * q₀) = x ^ g.1.1 * (y ^ (q₀ * q₁)) ^ (g.1.2 : ℕ) by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm q₁ q₀, mul_comm g.1.1, pow_mul, ht,
      mul_comm (g.1.2 : ℕ), pow_mul]]
  ring


omit [Fintype k] in
theorem add_pow_card_pow' [Fintype k] {R : Type*} [CommRing R] [Algebra k R] (m : ℕ) (x y : R) :
    (x + y) ^ (Fintype.card k ^ m) = x ^ (Fintype.card k ^ m) + y ^ (Fintype.card k ^ m) := by
  rw [← frobeniusAlgHom_pow_apply, ← frobeniusAlgHom_pow_apply, ← frobeniusAlgHom_pow_apply,
    map_add]

include hw in
/-- **Upper bound for the points over `𝔽_Q`** (`Q = q ^ (m₀ + m₁)`), for parameters `a, b`
satisfying Bombieri's two inequalities. -/
theorem card_fixed_le [IsDomain (AdjoinRoot (baseChange L F))]
    (ψ : AdjoinRoot (baseChange L F) →ₐ[L] L⟦X⟧) (c : L)
    (hψ : ψ (AdjoinRoot.of _ X) = PowerSeries.C c + PowerSeries.X)
    {a b m₀ m₁ : ℕ} (ha : F.natDegree * a + w * F.natDegree * F.natDegree < Fintype.card k ^ m₁)
    (hV : F.natDegree * (Fintype.card k ^ m₀ * a + b + 1) <
      (idx F w b).card * Module.finrank k (filt hF w a))
    (M : Type*) [Field M] [Algebra k M] :
    {φ : AdjoinRoot F →ₐ[k] M |
        φ (AdjoinRoot.of F X) ^ (Fintype.card k ^ (m₀ + m₁)) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (Fintype.card k ^ (m₀ + m₁)) = φ (AdjoinRoot.root F)}.Finite ∧
    {φ : AdjoinRoot F →ₐ[k] M |
        φ (AdjoinRoot.of F X) ^ (Fintype.card k ^ (m₀ + m₁)) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (Fintype.card k ^ (m₀ + m₁)) = φ (AdjoinRoot.root F)}.ncard ≤
      F.natDegree * (a + Fintype.card k ^ m₁ * b) + w * F.natDegree * F.natDegree := by
  classical
  set q := Fintype.card k
  set B := monoBasis hF
  let Fr₀ := FiniteField.frobeniusAlgHom k (AdjoinRoot F) ^ m₀
  have hFr₀ : ∀ x, Fr₀ x = x ^ q ^ m₀ := frobeniusAlgHom_pow_apply m₀
  let Φ₀ : (idx F w b → filt hF w a) →ₗ[k] AdjoinRoot F :=
    ∑ g : idx F w b, LinearMap.mulRight k (B g) ∘ₗ Fr₀.toLinearMap ∘ₗ (filt hF w a).subtype ∘ₗ
      LinearMap.proj g
  have hΦ₀ : ∀ f, Φ₀ f = ∑ g : idx F w b, (f g : AdjoinRoot F) ^ q ^ m₀ * B g := by
    intro f
    simp [Φ₀, hFr₀]
  have hmem : ∀ f, Φ₀ f ∈ filt hF w (q ^ m₀ * a + b) := by
    intro f
    rw [hΦ₀]
    exact Submodule.sum_mem _ fun g _ => mul_mem_filt hF hw (pow_mem_filt hF hw (f g).2 _)
      (monoBasis_mem_filt hF (mem_idx.1 g.2))
  let Φ := Φ₀.codRestrict _ hmem
  refine card_le_of_ker hF hw ψ c hψ ha Φ ?_ _ ?_
  · exact (finrank_filt_le hF w _).trans_lt hV
  · intro f hf φ hφ
    have hf0 : Φ₀ f = 0 := by
      have := congrArg Subtype.val ((LinearMap.mem_ker).1 hf)
      simpa [Φ] using this
    have hq0 : q ^ m₀ ≠ 0 := pow_ne_zero _ Fintype.card_pos.ne'
    rw [← pow_eq_zero_iff hq0, frob_identity hF φ (q₀ := q ^ m₀) (q₁ := q ^ m₁)
      (by rw [← pow_add]; exact hφ.1) (add_pow_card_pow' m₀) _]
    rw [← pow_add, hφ.2, ← map_zero φ, ← hf0, hΦ₀, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [monoBasis_apply, ← mul_assoc, map_mul, map_mul, map_mul, map_pow φ (AdjoinRoot.root F)]


end Count

section Quotient

variable {k : Type*} [Field k] {F : k[X][X]} (hF : F.Monic)

/-- The quotient `F(Y) / (Y - y)` in `A[Y]`, `A = k[t][Y]/F`; its coefficients are the vector
that cuts out the off-diagonal part of `X ×_{ℙ¹} X`. -/
noncomputable def quot (F : k[X][X]) : (AdjoinRoot F)[X] :=
  (F.map (AdjoinRoot.of F)) /ₘ (X - C (AdjoinRoot.root F))

theorem X_sub_C_mul_quot : (X - C (AdjoinRoot.root F)) * quot F = F.map (AdjoinRoot.of F) :=
  mul_divByMonic_eq_iff_isRoot.2 (AdjoinRoot.isRoot_root F)

include hF in
theorem quot_monic : (quot F).Monic :=
  (monic_X_sub_C _).of_mul_monic_left (by rw [X_sub_C_mul_quot]; exact hF.map _)

include hF in
theorem natDegree_quot [Nontrivial (AdjoinRoot F)] : (quot F).natDegree + 1 = F.natDegree := by
  have h := congrArg natDegree (X_sub_C_mul_quot (F := F))
  rw [(monic_X_sub_C _).natDegree_mul (quot_monic hF), natDegree_X_sub_C,
    hF.natDegree_map] at h
  omega

include hF in
theorem coeff_quot_pred [Nontrivial (AdjoinRoot F)] :
    (quot F).coeff (F.natDegree - 1) = 1 := by
  have h := natDegree_quot hF
  rw [show F.natDegree - 1 = (quot F).natDegree by omega]
  exact quot_monic hF

end Quotient

section Moved

variable {k : Type*} [Field k] [Fintype k] {L : Type*} [Field L] [Algebra k L]
  {F : k[X][X]} (hF : F.Monic) {w : ℕ}
  (hw : ∀ i < F.natDegree, (F.coeff i).natDegree ≤ (F.natDegree - i) * w)

include hw in
/-- **Upper bound for the moved points**: the `φ` with `φ (t) ∈ 𝔽_Q` but `φ (y) ∉ 𝔽_Q`, i.e. the
points `x` with `t (Frob x) = t (x)`, `Frob x ≠ x`. These are the twisted points of the
off-diagonal correspondence of `X ×_{ℙ¹} X`, which has degree `d - 1` over `X`; Bombieri's
argument with the linear condition `β_i = quot_i · β_{d-1}` bounds them by `(d - 1) Q + O(√Q)`. -/
theorem card_moved_le [IsDomain (AdjoinRoot (baseChange L F))]
    (ψ : AdjoinRoot (baseChange L F) →ₐ[L] L⟦X⟧) (c : L)
    (hψ : ψ (AdjoinRoot.of _ X) = PowerSeries.C c + PowerSeries.X)
    (hd : 0 < F.natDegree) {N₀ : ℕ} (hN₀ : ∀ i, (quot F).coeff i ∈ filt hF w N₀)
    {a b m₀ m₁ : ℕ} (ha : F.natDegree * a + w * F.natDegree * F.natDegree < Fintype.card k ^ m₁)
    (hV : (F.natDegree - 1) * (F.natDegree * (Fintype.card k ^ m₀ * a + b + N₀ + 1)) <
      (idx F w b).card * Module.finrank k (filt hF w a))
    (M : Type*) [Field M] [Algebra k M] :
    {φ : AdjoinRoot F →ₐ[k] M |
        φ (AdjoinRoot.of F X) ^ (Fintype.card k ^ (m₀ + m₁)) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (Fintype.card k ^ (m₀ + m₁)) ≠ φ (AdjoinRoot.root F)}.Finite ∧
    {φ : AdjoinRoot F →ₐ[k] M |
        φ (AdjoinRoot.of F X) ^ (Fintype.card k ^ (m₀ + m₁)) = φ (AdjoinRoot.of F X) ∧
        φ (AdjoinRoot.root F) ^ (Fintype.card k ^ (m₀ + m₁)) ≠ φ (AdjoinRoot.root F)}.ncard ≤
      F.natDegree * (a + Fintype.card k ^ m₁ * b) + w * F.natDegree * F.natDegree := by
  classical
  have hdom := isDomain_of_baseChange L hF
  set q := Fintype.card k
  set d := F.natDegree with hd_def
  let Fr₀ := FiniteField.frobeniusAlgHom k (AdjoinRoot F) ^ m₀
  have hFr₀ : ∀ x, Fr₀ x = x ^ q ^ m₀ := frobeniusAlgHom_pow_apply m₀
  let last : Fin d := ⟨d - 1, by omega⟩
  let β : Fin d → ((idx F w b → filt hF w a) →ₗ[k] AdjoinRoot F) := fun i =>
    ∑ g ∈ Finset.univ.filter (fun g : idx F w b => g.1.2 = i),
      LinearMap.mulRight k (AdjoinRoot.of F (X ^ g.1.1)) ∘ₗ Fr₀.toLinearMap ∘ₗ
        (filt hF w a).subtype ∘ₗ LinearMap.proj g
  have hβ : ∀ i f, β i f = ∑ g ∈ Finset.univ.filter (fun g : idx F w b => g.1.2 = i),
      (f g : AdjoinRoot F) ^ q ^ m₀ * AdjoinRoot.of F (X ^ g.1.1) := by
    intro i f
    simp [β, hFr₀]
  have hβmem : ∀ i f, β i f ∈ filt hF w (q ^ m₀ * a + b) := by
    intro i f
    rw [hβ]
    refine Submodule.sum_mem _ fun g _ => mul_mem_filt hF hw (pow_mem_filt hF hw (f g).2 _) ?_
    have h1 := of_mem_filt hF hw (X ^ g.1.1)
    rw [natDegree_X_pow] at h1
    exact filt_mono hF w (by have := mem_idx.1 g.2; omega) h1
  set N₂ := q ^ m₀ * a + b + N₀
  let comp : Fin (d - 1) → ((idx F w b → filt hF w a) →ₗ[k] filt hF w N₂) := fun i =>
    (β ⟨i, by omega⟩ - LinearMap.mulLeft k ((quot F).coeff i) ∘ₗ β last).codRestrict _
      (fun f => Submodule.sub_mem _ (filt_mono hF w (by omega) (hβmem _ f))
        (filt_mono hF w (by omega) (mul_mem_filt hF hw (hN₀ i) (hβmem last f))))
  let Φ : (idx F w b → filt hF w a) →ₗ[k] (Fin (d - 1) → filt hF w N₂) := LinearMap.pi comp
  refine card_le_of_ker hF hw ψ c hψ ha Φ ?_ _ ?_
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (finrank_filt_le hF w N₂)) hV
  · intro f hf φ hφ
    obtain ⟨ht, hy⟩ := hφ
    set Q := q ^ (m₀ + m₁)
    set η₁ := φ (AdjoinRoot.root F)
    set η₂ := η₁ ^ Q
    -- the linear condition, for every index
    have hβeq : ∀ i : Fin d, β i f = (quot F).coeff i * β last f := by
      intro i
      by_cases hi : (i : ℕ) < d - 1
      · have h1 := congrArg (fun v => ((v ⟨i, hi⟩ : filt hF w N₂) : AdjoinRoot F))
          ((LinearMap.mem_ker).1 hf)
        simp only [Φ, comp, LinearMap.pi_apply, LinearMap.codRestrict_apply,
          LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Pi.zero_apply,
          ZeroMemClass.coe_zero] at h1
        rw [← sub_eq_zero, ← h1]
      · have hil : i = last := Fin.ext (by simp [last]; omega)
        subst hil
        rw [show ((last : Fin d) : ℕ) = d - 1 from rfl, coeff_quot_pred hF, one_mul]
    -- `F(c, η₂) = 0` with `c = φ t`
    have hroot : ((quot F).map φ.toRingHom).eval η₂ = 0 := by
      let φ' : AdjoinRoot F →ₐ[k] M := (FiniteField.frobeniusAlgHom k M ^ (m₀ + m₁)).comp φ
      have hφ' : ∀ x, φ' x = φ x ^ Q := fun x => frobeniusAlgHom_pow_apply _ _
      have hcomp : φ.toRingHom.comp (AdjoinRoot.of F) = φ'.toRingHom.comp (AdjoinRoot.of F) := by
        apply Polynomial.ringHom_ext
        · intro a
          have e : AdjoinRoot.of F (C a) = algebraMap k (AdjoinRoot F) a := by
            rw [IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot F), Polynomial.algebraMap_eq,
              AdjoinRoot.algebraMap_eq]
          simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
            RingHom.coe_coe, e, AlgHom.commutes]
        · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
            RingHom.coe_coe, hφ', ht]
      have hF0 : ((F.map (AdjoinRoot.of F)).map φ.toRingHom).eval η₂ = 0 := by
        have key := Polynomial.hom_eval₂ (p := F) (f := AdjoinRoot.of F) (g := φ'.toRingHom)
          (AdjoinRoot.root F)
        rw [AdjoinRoot.eval₂_root, map_zero] at key
        rw [Polynomial.map_map, hcomp, eval_map, key]
        congr 1
        exact (hφ' _).symm
      have h2 := congrArg (fun p => (p.map φ.toRingHom).eval η₂) (X_sub_C_mul_quot (F := F))
      simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, eval_mul, eval_sub,
        eval_X, eval_C] at h2
      rw [hF0] at h2
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hy)
    have hq0 : q ^ m₀ ≠ 0 := pow_ne_zero _ Fintype.card_pos.ne'
    rw [← pow_eq_zero_iff hq0, frob_identity hF φ (q₀ := q ^ m₀) (q₁ := q ^ m₁)
      (by rw [← pow_add]; exact ht) (add_pow_card_pow' m₀) _, ← pow_add]
    rw [← Finset.sum_fiberwise Finset.univ (fun g : idx F w b => g.1.2)]
    have hfib : ∀ i : Fin d, ∑ g ∈ Finset.univ.filter (fun g : idx F w b => g.1.2 = i),
        φ ((f g : AdjoinRoot F) ^ q ^ m₀ * AdjoinRoot.of F (X ^ g.1.1)) * η₂ ^ (g.1.2 : ℕ) =
        φ ((quot F).coeff i) * φ (β last f) * η₂ ^ (i : ℕ) := by
      intro i
      rw [← map_mul, ← hβeq, hβ, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.1 hg).2]
    rw [Finset.sum_congr rfl fun i _ => hfib i]
    have hsum : ∑ i : Fin d, φ ((quot F).coeff i) * φ (β last f) * η₂ ^ (i : ℕ) =
        φ (β last f) * ((quot F).map φ.toRingHom).eval η₂ := by
      have hdeg : ((quot F).map φ.toRingHom).natDegree < d := by
        have := natDegree_quot hF
        have := natDegree_map_le (f := φ.toRingHom) (p := quot F)
        omega
      rw [eval_eq_sum_range' hdeg, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coeff_map]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    rw [hsum, hroot, mul_zero]

end Moved

end RiemannMasullo.WeilBound
