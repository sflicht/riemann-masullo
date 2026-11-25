module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.PSeries
import RiemannMasullo.ForMathlib.Analysis.Complex.LandauLemma

/-!
# Summability of zeros in a vertical strip

Jensen's inequality on fixed-radius discs gives a logarithmic bound for the number of
zeros at each large height when the function and its reciprocal at the centers have polynomial
growth. Summing these bounds with an inverse-square weight counts zeros with multiplicity.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped Asymptotics Topology

namespace RiemannMasullo

local notation "atAbsTop" => comap (abs : ℝ → ℝ) atTop
local notation "atHeight" => comap (abs ∘ Complex.im) atTop
set_option quotPrecheck false in
local notation "StripGrowth(" f ")" =>
  ∀ a b : ℝ, a < b → ∃ M : ℝ, 0 < M ∧
    (f : ℂ → ℂ) =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z : ℂ ↦ |Complex.im z| ^ M
set_option quotPrecheck false in
local notation "InverseGrowth(" f ", " σ ", " k ")" =>
  (fun t : ℝ ↦ ((f : ℂ → ℂ) ⟨σ, t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ (k : ℕ))
set_option quotPrecheck false in
local notation "windowZeros(" f ", " b ", " a ")" =>
  {z : ℂ // 0 < MeromorphicOn.divisor (f : ℂ → ℂ) univ z ∧ |Complex.re z - (b : ℝ)| < (a : ℝ)}

/-- A uniform square-root bound for the mass in each unit height bin
bounds the inverse-square moment by a constant times the convergent
three-halves power series. -/
theorem tsum_zeroWeights_le_of_bins {ι : Type*}
    (h m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (C : ℝ)
    (hcount : ∀ (n : ℕ) (S : Finset ι), (∀ i ∈ S, ⌊|h i|⌋₊ = n) →
      ∑ i ∈ S, m i ≤ C * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) :
    Summable (fun i ↦ m i / (1 + |h i|) ^ 2) ∧
      (∑' i, m i / (1 + |h i|) ^ 2) ≤ C * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  classical
  let b (i : ι) := ⌊|h i|⌋₊
  let u (n : ℕ) := C / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
  have hu : Summable u := by
    have h := ((Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)).mul_left C
    simpa [u, abs_of_nonneg, add_nonneg, div_eq_mul_inv] using h
  have hC : 0 ≤ C := by simpa using hcount 0 ∅ (by simp)
  suffices hbound : ∀ S : Finset ι, (∑ i ∈ S, m i / (1 + |h i|) ^ 2) ≤ ∑' n, u n by
    have hnon (i) : 0 ≤ m i / (1 + |h i|) ^ 2 := div_nonneg (hm i) (sq_nonneg _)
    refine ⟨summable_of_sum_le hnon hbound, (Real.tsum_le_of_sum_le hnon hbound).trans_eq ?_⟩
    simp only [u, div_eq_mul_inv, one_mul, tsum_mul_left]
  intro S
  have hf (n : ℕ) : ∑ i ∈ S with b i = n, m i / (1 + |h i|) ^ 2 ≤ u n := by
    let T := S.filter (fun i ↦ b i = n)
    have ht : ∀ i ∈ T, ⌊|h i|⌋₊ = n := fun i hi ↦ (Finset.mem_filter.mp hi).2
    have hn : 0 < (n : ℝ) + 1 := by positivity
    calc
      _ ≤ ∑ i ∈ T, m i / ((n : ℝ) + 1)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have he : b i = n := (Finset.mem_filter.mp hi).2
        have hle : (n : ℝ) ≤ |h i| := he ▸ Nat.floor_le (abs_nonneg _)
        exact div_le_div_of_nonneg_left (hm i) (sq_pos_of_pos hn)
          (pow_le_pow_left₀ hn.le (by linarith) 2)
      _ = (∑ i ∈ T, m i) / ((n : ℝ) + 1)^2 := by simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ C * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) / ((n : ℝ) + 1)^2 :=
        div_le_div_of_nonneg_right (hcount n T ht) (sq_nonneg _)
      _ = u n := by
        rw [show (((n : ℝ) + 1)^2) = ((n : ℝ) + 1)^(2 : ℝ) from (Real.rpow_two _).symm,
          mul_div_assoc, ← Real.rpow_sub hn, show (1 : ℝ)/2-2 = -(3/2) by norm_num, Real.rpow_neg hn.le]
        rfl
  calc
    _ = ∑ n ∈ S.image b, ∑ i ∈ S with b i = n, m i / (1 + |h i|) ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_image_of_mem b hi) _).symm
    _ ≤ ∑ n ∈ S.image b, u n := Finset.sum_le_sum (fun n _ ↦ hf n)
    _ ≤ ∑' n, u n := hu.sum_le_tsum _ fun _ _ ↦ div_nonneg hC (Real.rpow_nonneg (by positivity) _)

/-- A square-root bound on the total weight in each unit height range gives a summable inverse-
square weight. -/
private theorem summable_zeroWeights_of_bins {ι : Type*}
    (h m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (C : ℝ)
    (hcount : ∀ (n : ℕ) (S : Finset ι), (∀ i ∈ S, ⌊|h i|⌋₊ = n) →
      ∑ i ∈ S, m i ≤ C * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) :
    Summable (fun i ↦ m i / (1 + |h i|) ^ 2) :=
  (tsum_zeroWeights_le_of_bins h m hm C hcount).1

/-- Jensen’s inequality bounds the sum of orders on any finite subset of the smaller disc. -/
private theorem zeroCount_disk_sum {f : ℂ → ℂ} {c : ℂ} {r R B : ℝ}
    (hr : 0 < r) (hrR : r < R) (ha : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hB : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c r) :
    ∑ z ∈ S, (analyticOrderNatAt f z : ℝ) ≤ Real.log B / Real.log (R / r) := by
  classical
  let W := {z : ℂ | z ∈ closedBall c r ∧ f z = 0}
  have hW : W.Finite := finite_zeros_closedBall hr.le (ha.mono (closedBall_subset_closedBall hrR.le)) hc
  let points := hW.toFinset ∪ S
  have heq : ∑ᶠ z ∈ closedBall c r, (analyticOrderNatAt f z : ℝ) = ∑ z ∈ points, (analyticOrderNatAt f z : ℝ) := by
    rw [← finsum_mem_coe_finset]
    apply finsum_mem_inter_support_eq'
    intro z hz
    have hzero : f z = 0 := by
      by_contra hne
      exact hz (by simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hne)])
    change z ∈ closedBall c r ↔ z ∈ points
    refine ⟨fun h ↦ Finset.mem_union_left _ (hW.mem_toFinset.mpr ⟨h, hzero⟩), ?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (hW.mem_toFinset.mp h).1
    · exact hS z h
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right (s₁ := hW.toFinset))
    (fun _ _ _ ↦ Nat.cast_nonneg _)) ?_
  rw [← heq]
  exact landau_sum_analyticOrderNatAt_le hr hrR ha hc hB

/-- An upper bound on meromorphic order gives the same bound on the completed divisor at each
point of the disc. -/
private theorem zeroCount_local_order {L Λ : ℂ → ℂ} (hΛ : MeromorphicOn Λ univ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : AnalyticOnNhd ℂ L (closedBall c R)) (hc : L c ≠ 0)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z) {z : ℂ} (hz : z ∈ closedBall c R) :
    (MeromorphicOn.divisor Λ univ z : ℝ) ≤ analyticOrderNatAt L z := by
  have hbase : analyticOrderAt L c ≠ ⊤ := by
    rw [(ha c (mem_closedBall_self hR)).analyticOrderAt_eq_zero.mpr hc]
    simp
  have hf := ha.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected (mem_closedBall_self hR) hz hbase
  have ho : meromorphicOrderAt L z = ((analyticOrderNatAt L z : ℤ) : WithTop ℤ) := by
    rw [(ha z hz).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hf, ENat.map_natCast]
  rw [MeromorphicOn.divisor_apply hΛ (mem_univ _)]
  have h := hcmp z
  rw [ho] at h
  have : (meromorphicOrderAt Λ z).untop₀ ≤ (analyticOrderNatAt L z : ℤ) := by
    simpa using WithTop.untop₀_le_untop₀ (WithTop.coe_ne_top : ((analyticOrderNatAt L z : ℤ) : WithTop ℤ) ≠ ⊤) h
  exact_mod_cast this

/-- Jensen's inequality bounds a finite sum of divisor multiplicities by the
growth of an analytic comparison function whose local orders dominate them. -/
theorem sum_divisor_le_log_of_disk_bound {Λ L : ℂ → ℂ} (hΛ : MeromorphicOn Λ univ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    {c : ℂ} {r R B : ℝ} (hr : 0 < r) (hrR : r < R)
    (ha : AnalyticOnNhd ℂ L (closedBall c R)) (hc : L c ≠ 0)
    (hB : ∀ z ∈ closedBall c R, ‖L z / L c‖ ≤ B)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall c r) :
    ∑ z ∈ S, (MeromorphicOn.divisor Λ univ z : ℝ) ≤ Real.log B / Real.log (R / r) := by
  apply le_trans (Finset.sum_le_sum fun z hz ↦
    zeroCount_local_order hΛ (hr.trans hrR).le ha hc hcmp
      (closedBall_subset_closedBall hrR.le (hS z hz)))
  exact zeroCount_disk_sum hr hrR ha hc hB S hS

private theorem zeroCount_compact {f : ℂ → ℂ} (K : Set ℂ) (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ MeromorphicOn.divisor f univ z ≠ 0}.Finite := by
  let D := MeromorphicOn.divisor f univ
  have h := (D.restrict (subset_univ K)).finiteSupport hK
  apply h.subset
  intro z hz
  change (D.restrict (subset_univ K)) z ≠ 0
  simpa [locallyFinsuppWithin.restrict, hz.1, D] using hz.2

/-- Polynomial growth in a slightly wider strip rules out poles at sufficiently large absolute
height. -/
private theorem zeroCount_polynomial_strip {L : ℂ → ℂ} (σ : ℝ) (hL : MeromorphicNFOn L univ)
    (hGrowth : StripGrowth(L)) (R : ℝ) (hR : 0 < R) :
    ∃ C M T : ℝ, 0 < C ∧ 0 < M ∧ ∀ z : ℂ, |z.re - σ| ≤ R → T < |z.im| →
      AnalyticAt ℂ L z ∧ ‖L z‖ ≤ C * |z.im| ^ M := by
  let a := σ - R - 1
  let b := σ + R + 1
  obtain ⟨M, hM, hg⟩ := hGrowth a b (by dsimp [a, b]; linarith)
  obtain ⟨C, hC, hg⟩ := Asymptotics.isBigO_iff'.mp hg
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hg
  obtain ⟨T, hT⟩ := hg
  have hB (z : ℂ) (hz : z.re ∈ Icc a b) (ht : T ≤ |z.im|) :
      ‖L z‖ ≤ C * |z.im| ^ M := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hT _ ht z rfl hz
  refine ⟨C, M, T, hC, hM, fun z hz ht ↦ ⟨?_, hB _ ⟨?_, ?_⟩ ht.le⟩⟩ <;>
    try first | (dsimp [a, b]; linarith [(abs_le.mp hz).1, (abs_le.mp hz).2])
  apply (hL (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  have hr : z.re ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
  have him : Continuous (fun u : ℂ ↦ |u.im|) := Complex.continuous_im.abs
  have hn₁ := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hr
  have hn₂ : ∀ᶠ u : ℂ in 𝓝 z, |u.im| ∈ Ioo T (|z.im| + 1) :=
    (isOpen_Ioo.preimage him).mem_nhds ⟨ht, by linarith⟩
  have hbnd : ∀ᶠ u : ℂ in 𝓝 z, ‖L u‖ ≤ C * (|z.im| + 1) ^ M := by
    filter_upwards [hn₁, hn₂] with u hu hv
    exact (hB u ⟨hu.1.le, hu.2.le⟩ hv.1.le).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hv.2.le hM.le) hC.le)
  have hinf := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop (C * (|z.im| + 1) ^ M)
  obtain ⟨u, hu, hv⟩ := ((hbnd.filter_mono nhdsWithin_le_nhds).and hinf).exists
  exact (not_lt_of_ge hu) hv

/-- The reciprocal estimate on the center line bounds the normalizing factor in Jensen’s
inequality. -/
private theorem zeroCount_center_bound {L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hne : ∀ᶠ t : ℝ in atAbsTop, L ⟨σ, t⟩ ≠ 0) (hinv : InverseGrowth(L, σ, k)) :
    ∃ D T : ℝ, ∃ k : ℕ, 0 < D ∧ ∀ t : ℝ, T ≤ |t| →
      L ⟨σ, t⟩ ≠ 0 ∧ ‖(L ⟨σ, t⟩)⁻¹‖ ≤ D * |t| ^ k := by
  obtain ⟨D, hD, hb⟩ := Asymptotics.isBigO_iff'.mp hinv
  have h := hne.and hb
  rw [eventually_comap, eventually_atTop] at h
  obtain ⟨T, hT⟩ := h
  refine ⟨D, T, k, hD, fun t ht ↦ ⟨(hT _ ht t rfl).1, ?_⟩⟩
  simpa using (hT _ ht t rfl).2

/-- A fixed-radius disc centered at `σ + it` has a polynomial bound relative to its center value,
uniformly at large absolute height. -/
private theorem zeroCount_disk_growth {L : ℂ → ℂ} {σ : ℝ} {k : ℕ} (hL : MeromorphicNFOn L univ)
    (hGrowth : StripGrowth(L)) (hne : ∀ᶠ t : ℝ in atAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : InverseGrowth(L, σ, k)) (R : ℝ) (hR : 0 < R) :
    ∃ B E T : ℝ, 0 < B ∧ 0 ≤ E ∧ ∀ t : ℝ, T ≤ |t| →
      let c : ℂ := ⟨σ, t⟩
      AnalyticOnNhd ℂ L (Metric.closedBall c R) ∧ L c ≠ 0 ∧
        ∀ z ∈ Metric.closedBall c R, ‖L z / L c‖ ≤ B * (1 + |t|) ^ E := by
  obtain ⟨C, M, T, hC, hM, hg⟩ := zeroCount_polynomial_strip σ hL hGrowth R hR
  obtain ⟨D, T', k, hD, hd⟩ := zeroCount_center_bound hne hinv
  let windowFactor := (1 + R) ^ M
  refine ⟨C * windowFactor * D, M + k, max (T + R + 1) T', mul_pos (mul_pos hC ?_) hD, by positivity, ?_⟩
  · exact Real.rpow_pos_of_pos (by linarith) _
  intro t ht c
  obtain ⟨hc, hci⟩ := hd t ((le_max_right _ _).trans ht)
  have hpoints {z : ℂ} (hz : z ∈ Metric.closedBall c R) :
      |z.re - σ| ≤ R ∧ T < |z.im| ∧ |z.im| ≤ (1 + R) * (1 + |t|) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre := (Complex.abs_re_le_norm (z - c)).trans hz
    have him := (Complex.abs_im_le_norm (z - c)).trans hz
    change |z.re - σ| ≤ R at hre
    change |z.im - t| ≤ R at him
    have hdiff := (abs_abs_sub_abs_le_abs_sub z.im t).trans him
    have ht' := (le_max_left _ T').trans ht
    refine ⟨hre, by linarith [(abs_le.mp hdiff).1], ?_⟩
    nlinarith [(abs_le.mp hdiff).2, mul_nonneg hR.le (abs_nonneg t)]
  refine ⟨fun z hz ↦ (hg z (hpoints hz).1 (hpoints hz).2.1).1, hc, fun z hz ↦ ?_⟩
  have h1 : 0 < 1 + |t| := by positivity
  have hV : 0 < windowFactor := Real.rpow_pos_of_pos (by linarith) _
  have hu := (hg z (hpoints hz).1 (hpoints hz).2.1).2
  have hv : |z.im| ^ M ≤ windowFactor * (1 + |t|) ^ M := by
    rw [← Real.mul_rpow (by linarith : 0 ≤ 1 + R) h1.le]
    exact Real.rpow_le_rpow (abs_nonneg _) (hpoints hz).2.2 hM.le
  have hi : ‖(L c)⁻¹‖ ≤ D * (1 + |t|) ^ k := hci.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (by linarith) k) hD.le)
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add h1, Real.rpow_natCast]
  calc
    _ ≤ (C * (windowFactor * (1 + |t|)^M)) * (D * (1 + |t|)^k) :=
      mul_le_mul (hu.trans (mul_le_mul_of_nonneg_left hv hC.le)) hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The logarithm in Jensen’s inequality is bounded by a constant times the square root of the
height. -/
private theorem zeroCount_log_bound (B E r R : ℝ) (hB : 0 < B) (hE : 0 ≤ E)
    (hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 1 ≤ u →
      Real.log (B * u ^ E) / Real.log (R / r) ≤ K * u ^ (1 / 2 : ℝ) := by
  let D := Real.log (R / r)
  have hD : 0 < D := Real.log_pos ((one_lt_div hr).mpr hrR)
  refine ⟨(max (Real.log B) 0 + 2 * E)/D, div_nonneg (by positivity) hD.le, fun u hu ↦ ?_⟩
  have hpos : 0 < u := zero_lt_one.trans_le hu
  have hv : 1 ≤ u ^ (1 / 2 : ℝ) := Real.one_le_rpow hu (by norm_num)
  have hl : Real.log u ≤ 2 * u ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos (1 / 2 : ℝ))
    rw [Real.log_rpow hpos] at h
    linarith
  rw [Real.log_mul hB.ne' (Real.rpow_pos_of_pos hpos E).ne', Real.log_rpow hpos]
  change _ / D ≤ _ / D * _
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hD]
  nlinarith [mul_le_mul_of_nonneg_left hl hE,
    mul_le_mul_of_nonneg_left hv (le_max_right (Real.log B) 0), le_max_left (Real.log B) 0]

/-- Compare a finite set of zeros in a horizontal rectangle with a
single Jensen disk, retaining the logarithm of the center-normalized bound. -/
private theorem zeroCount_window_jensen {Λ L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hΛ : MeromorphicOn Λ univ) (hL : MeromorphicNFOn L univ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    (hGrowth : StripGrowth(L)) (hne : ∀ᶠ t : ℝ in atAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : InverseGrowth(L, σ, k)) (b a : ℝ) :
    ∃ B E T r R : ℝ, 0 < B ∧ 0 ≤ E ∧ 0 < r ∧ r < R ∧
      ∀ t : ℝ, T ≤ |t| → ∀ S : Finset (windowZeros(Λ, b, a)),
        (∀ z ∈ S, |z.val.im - t| ≤ 1) →
        ∑ z ∈ S, (MeromorphicOn.divisor Λ univ z.val : ℝ) ≤
          Real.log (B * (1 + |t|) ^ E) / Real.log (R / r) := by
  classical
  let r := |a| + |b - σ| + 2
  let R := r + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := lt_add_one _
  obtain ⟨B, E, T, hB, hE, hdata⟩ := zeroCount_disk_growth hL hGrowth hne hinv R (hr.trans hrR)
  refine ⟨B, E, T, r, R, hB, hE, hr, hrR, fun t ht S hS ↦ ?_⟩
  let c : ℂ := ⟨σ, t⟩
  obtain ⟨ha, hc, hbound⟩ := hdata t ht
  have hinside (z : windowZeros(Λ, b, a)) (hz : |z.val.im - t| ≤ 1) : z.val ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |z.val.re - σ| + |z.val.im - t| ≤ |a| + |b - σ| + 2
    have hre : |z.val.re - σ| ≤ |a| + |b - σ| := calc
      _ = |(z.val.re - b) + (b - σ)| := by rw [sub_add_sub_cancel]
      _ ≤ _ := (abs_add_le ..).trans
        (add_le_add (z.property.2.le.trans (le_abs_self a)) le_rfl)
    linarith
  let emb : windowZeros(Λ, b, a) ↪ ℂ := Function.Embedding.subtype _
  have hmem : ∀ z ∈ S.map emb, z ∈ closedBall c r := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
    exact hinside i (hS i hi)
  simpa only [Finset.sum_map, emb, Function.Embedding.coe_subtype] using
    sum_divisor_le_log_of_disk_bound hΛ hcmp hr hrR ha hc hbound (S.map emb) hmem

/-- At all sufficiently large positive or negative heights, the total
multiplicity in a fixed-width rectangle of height two is at most a constant
times one plus the logarithm of the height. -/
theorem sum_divisor_le_log_height_window {Λ L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hΛ : MeromorphicOn Λ univ) (hL : MeromorphicNFOn L univ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    (hGrowth : StripGrowth(L)) (hne : ∀ᶠ t : ℝ in atAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : InverseGrowth(L, σ, k)) (b a : ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ ∀ t : ℝ, T ≤ |t| → ∀ S : Finset (windowZeros(Λ, b, a)),
      (∀ z ∈ S, |z.val.im - t| ≤ 1) →
      ∑ z ∈ S, (MeromorphicOn.divisor Λ univ z.val : ℝ) ≤ K * (1 + Real.log (1 + |t|)) := by
  obtain ⟨B, E, T, r, R, hB, hE, hr, hrR, hcount⟩ :=
    zeroCount_window_jensen hΛ hL hcmp hGrowth hne hinv b a
  have hd : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  refine ⟨(|Real.log B| + E) / Real.log (R/r), T, div_nonneg (add_nonneg (abs_nonneg _) hE) hd.le,
    fun t ht S hS ↦ (hcount t ht S hS).trans ?_⟩
  have ht₁ : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hp := zero_lt_one.trans_le ht₁
  rw [Real.log_mul hB.ne' (Real.rpow_pos_of_pos hp E).ne', Real.log_rpow hp,
    div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd]
  nlinarith [le_abs_self (Real.log B), mul_nonneg (abs_nonneg (Real.log B)) (Real.log_nonneg ht₁)]

/-- Jensen's formula bounds the total multiplicity in a fixed-width rectangle of height two. -/
private theorem zeroCount_window_at_height {Λ L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hΛ : MeromorphicOn Λ univ) (hL : MeromorphicNFOn L univ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    (hGrowth : StripGrowth(L)) (hne : ∀ᶠ t : ℝ in atAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : InverseGrowth(L, σ, k)) (b a : ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ ∀ t : ℝ, T ≤ |t| → ∀ S : Finset (windowZeros(Λ, b, a)),
      (∀ z ∈ S, |z.val.im - t| ≤ 1) →
      ∑ z ∈ S, (MeromorphicOn.divisor Λ univ z.val : ℝ) ≤ K * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨B, E, T, r, R, hB, hE, hr, hrR, hcount⟩ :=
    zeroCount_window_jensen hΛ hL hcmp hGrowth hne hinv b a
  obtain ⟨K, hK, hlog⟩ := zeroCount_log_bound B E r R hB hE hr hrR
  exact ⟨K, T, hK, fun t ht S hS ↦
    (hcount t ht S hS).trans (hlog _ (by linarith [abs_nonneg t]))⟩

/-- In a fixed vertical strip, the positive orders of a meromorphic function are summable
with weight `(1 + |Im z|)⁻²` if they are bounded by the orders of a meromorphic function of
polynomial growth on fixed strips, with eventual nonvanishing and polynomial reciprocal
growth on a fixed vertical line `σ + it`. The strip has center `b` and half-width `a`. -/
theorem summable_divisor_div_one_add_abs_im_sq {Λ L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hΛ : MeromorphicOn Λ univ) (hL : MeromorphicNFOn L univ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    (hGrowth : StripGrowth(L)) (hne : ∀ᶠ t : ℝ in atAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : InverseGrowth(L, σ, k)) (b a : ℝ) :
    Summable (fun z : windowZeros(Λ, b, a) ↦
      (MeromorphicOn.divisor Λ univ z.val : ℝ) / (1 + |z.val.im|) ^ 2) := by
  classical
  obtain ⟨K, T, hK, hhi⟩ := zeroCount_window_at_height hΛ hL hcmp hGrowth hne hinv b a
  let D := MeromorphicOn.divisor (Λ) univ
  let R := |a| + |b| + max T 0 + 2
  let Z := zeroCount_compact (f := Λ) (closedBall 0 R) (isCompact_closedBall _ _)
  let B := ∑ z ∈ Z.toFinset, max (D z : ℝ) 0
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ le_max_right _ _)
  apply summable_zeroWeights_of_bins (fun z : windowZeros(Λ, b, a) ↦ z.val.im)
    (fun z ↦ (D z.val : ℝ)) (fun z ↦ by exact_mod_cast z.property.1.le) (max B (2 * K))
  intro n S hS
  have hbin (z : windowZeros(Λ, b, a)) (hz : z ∈ S) :
      (n : ℝ) ≤ |z.val.im| ∧ |z.val.im| < (n : ℝ) + 1 := by
    rw [← hS z hz]
    exact ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  have hu : 1 ≤ ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num)
  by_cases ht : T ≤ (n : ℝ)
  · let C (z : windowZeros(Λ, b, a)) := 0 ≤ z.val.im
    have hp := hhi n (by simpa using ht) (S.filter C) (by
      intro z hz
      obtain ⟨hzS, hpos⟩ := Finset.mem_filter.mp hz
      have he := hbin z hzS
      rw [abs_of_nonneg (show 0 ≤ z.val.im from hpos)] at he
      exact abs_le.mpr ⟨by linarith [he.1], by linarith [he.2]⟩)
    have hn := hhi (-(n : ℝ)) (by simpa using ht) (S.filter (fun z ↦ ¬ C z)) (by
      intro z hz
      obtain ⟨hzS, hneg⟩ := Finset.mem_filter.mp hz
      have he := hbin z hzS
      rw [abs_of_neg (lt_of_not_ge (show ¬ 0 ≤ z.val.im from hneg))] at he
      exact abs_le.mpr ⟨by linarith [he.2], by linarith [he.1]⟩)
    simp only [abs_neg, Nat.abs_cast, add_comm (1 : ℝ)] at hp hn
    have hsum := Finset.sum_filter_add_sum_filter_not S C (fun z ↦ (D z.val : ℝ))
    calc
      _ ≤ (2 * K) * (((n : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
        rw [← hsum]
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hsub : ∀ z ∈ S, z ∈ (fun z : windowZeros(Λ, b, a) ↦ z.val) ⁻¹' (Z.toFinset : Set ℂ) := by
      intro z hz
      change z.val ∈ Z.toFinset
      apply Z.mem_toFinset.mpr
      refine ⟨?_, z.property.1.ne'⟩
      rw [mem_closedBall_zero_iff]
      apply (Complex.norm_le_abs_re_add_abs_im _).trans
      have hre : |z.val.re| ≤ |a| + |b| := calc
        _ = |(z.val.re - b) + b| := by rw [sub_add_cancel]
        _ ≤ _ := (abs_add_le ..).trans
          (add_le_add (z.property.2.le.trans (le_abs_self a)) le_rfl)
      dsimp [R]
      linarith [(hbin z hz).2, le_max_left T 0, lt_of_not_ge ht]
    let emb : windowZeros(Λ, b, a) ↪ ℂ := Function.Embedding.subtype _
    have hmap : S.map emb ⊆ Z.toFinset := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
      exact hsub i hi
    calc
      _ ≤ ∑ z ∈ S, max (D z.val : ℝ) 0 := Finset.sum_le_sum (fun _ _ ↦ le_max_left _ _)
      _ = ∑ z ∈ S.map emb, max (D z : ℝ) 0 := (Finset.sum_map S emb (fun z ↦ max (D z : ℝ) 0)).symm
      _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun _ _ _ ↦ le_max_right _ _)
      _ ≤ max B (2 * K) * (((n : ℝ) + 1) ^ (1 / 2 : ℝ)) :=
        (le_max_left _ _).trans (le_mul_of_one_le_right (hB.trans (le_max_left _ _)) hu)

end RiemannMasullo
