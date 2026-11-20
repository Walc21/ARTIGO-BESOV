import Formalizacao.AlturaBump

/-!
# Normas de Besov da função-teste e somas geométricas (auditoria, Parte II)

Para `f = bumpS φ a x₀ t` com `t ∈ (0,1]`, a sequência `2^{rs} ω_p(f, 2^{-r})` é dominada por
`κ x_r`, com `x_r` uniformemente `ℓ^q`-limitada (lema `tsum_split_le`), onde
`κ = K |a| (3t)^{1/p} t^{-s}`. Daí segue `‖f‖_{B^s_{p,q}} ≤ Λ |a| t^{1/p - s}` com `Λ` independente
de `a` e `t`. Esta é a cota de norma usada pelos pisos geométrico e de inclinação.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoAltura

open FormalizacaoLp FormalizacaoLow FormalizacaoRed

/-- Soma das duas séries geométricas que dominam `∑ x_r`, em `ENNReal`. -/
lemma tsum_split_le {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (n : ℕ) (x : ℕ → ℝ)
    (hx : ∀ r, 0 ≤ x r ∧ x r ≤ (if r ≤ n then α ^ (n - r) else 0) +
      (if n < r then β ^ (r - n - 1) else 0)) :
    ∑' r, ENNReal.ofReal (x r) ≤ ENNReal.ofReal (1 / (1 - α) + 1 / (1 - β)) := by
  set A : ℕ → ℝ := fun r => if r ≤ n then α ^ (n - r) else 0 with hAdef
  set B : ℕ → ℝ := fun r => if n < r then β ^ (r - n - 1) else 0 with hBdef
  have hA0 : ∀ r, 0 ≤ A r := fun r => by
    simp only [hAdef]; split_ifs <;> positivity
  have hB0 : ∀ r, 0 ≤ B r := fun r => by
    simp only [hBdef]; split_ifs <;> positivity
  -- parte `A`: suporte em `range (n+1)`, depois reflexão
  have hA : ∑' r, ENNReal.ofReal (A r) ≤ ENNReal.ofReal (1 / (1 - α)) := by
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · have hfin : ∑ r ∈ Finset.range (n + 1), ENNReal.ofReal (A r) =
          ∑ r ∈ Finset.range (n + 1), ENNReal.ofReal (α ^ (n - r)) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hr' : r ≤ n := by simp at hr; omega
        simp only [hAdef, if_pos hr']
      rw [hfin]
      have hrefl : ∑ r ∈ Finset.range (n + 1), ENNReal.ofReal (α ^ (n - r)) =
          ∑ r ∈ Finset.range (n + 1), ENNReal.ofReal (α ^ r) := by
        have := Finset.sum_range_reflect (fun k => ENNReal.ofReal (α ^ k)) (n + 1)
        simpa [Nat.add_sub_cancel] using this
      rw [hrefl]
      calc ∑ r ∈ Finset.range (n + 1), ENNReal.ofReal (α ^ r)
          ≤ ∑' r, ENNReal.ofReal (α ^ r) := ENNReal.sum_le_tsum _
        _ = ENNReal.ofReal (∑' r : ℕ, α ^ r) := by
            rw [ENNReal.ofReal_tsum_of_nonneg (fun r => pow_nonneg hα0 r)
              (summable_geometric_of_lt_one hα0 hα1)]
        _ = ENNReal.ofReal (1 / (1 - α)) := by
            rw [tsum_geometric_of_lt_one hα0 hα1, one_div]
    · intro r hr
      have : ¬ r ≤ n := by simp at hr; omega
      simp [hAdef, this]
  -- parte `B`: suporte em `{r > n}`, reindexação `i ↦ i + (n+1)`
  have hB : ∑' r, ENNReal.ofReal (B r) ≤ ENNReal.ofReal (1 / (1 - β)) := by
    have hinj : Function.Injective (fun i : ℕ => i + (n + 1)) := by
      intro i j hij; simp at hij; exact hij
    have hsupp : Function.support (fun r => ENNReal.ofReal (B r)) ⊆
        Set.range (fun i : ℕ => i + (n + 1)) := by
      intro r hr
      simp only [Function.mem_support] at hr
      have hgt : n < r := by
        by_contra hcon
        apply hr
        simp [hBdef, hcon]
      exact ⟨r - (n + 1), by simp; omega⟩
    rw [← hinj.tsum_eq hsupp]
    have hval : ∀ i : ℕ, ENNReal.ofReal (B (i + (n + 1))) = ENNReal.ofReal (β ^ i) := by
      intro i
      have hc : n < i + (n + 1) := by omega
      have e : i + (n + 1) - n - 1 = i := by omega
      simp only [hBdef, if_pos hc, e]
    simp only [hval]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => pow_nonneg hβ0 r)
      (summable_geometric_of_lt_one hβ0 hβ1), tsum_geometric_of_lt_one hβ0 hβ1, one_div]
  -- desigualdade final
  calc ∑' r, ENNReal.ofReal (x r)
      ≤ ∑' r, (ENNReal.ofReal (A r) + ENNReal.ofReal (B r)) := by
        apply ENNReal.tsum_le_tsum
        intro r
        rw [← ENNReal.ofReal_add (hA0 r) (hB0 r)]
        exact ENNReal.ofReal_le_ofReal (hx r).2
    _ = ∑' r, ENNReal.ofReal (A r) + ∑' r, ENNReal.ofReal (B r) := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (1 / (1 - α)) + ENNReal.ofReal (1 / (1 - β)) := add_le_add hA hB
    _ = ENNReal.ofReal (1 / (1 - α) + 1 / (1 - β)) :=
        (ENNReal.ofReal_add (by apply div_nonneg <;> linarith) (by apply div_nonneg <;> linarith)).symm

/-- Cota de `lqNorm` por `c·x_r` com soma de potências limitada (`q < ∞`). -/
lemma lqNorm_le_of_pow_sum {q : ℝ≥0∞} (hq0 : 0 < q) (hqt : q ≠ ⊤) (a : ℕ → ℝ≥0∞) {c : ℝ}
    (hc : 0 ≤ c) (x : ℕ → ℝ) (hx0 : ∀ r, 0 ≤ x r)
    (hax : ∀ r, a r ≤ ENNReal.ofReal (c * x r)) {D : ℝ} (hD : 0 ≤ D)
    (hsum : ∑' r, ENNReal.ofReal (x r ^ q.toReal) ≤ ENNReal.ofReal D) :
    lqNorm q a ≤ ENNReal.ofReal (c * D ^ q.toReal⁻¹) := by
  unfold lqNorm
  rw [if_neg hqt]
  set Q := q.toReal with hQdef
  have hQ : 0 < Q := ENNReal.toReal_pos hq0.ne' hqt
  have hpow : ∀ r, a r ^ Q ≤ ENNReal.ofReal (c ^ Q) * ENNReal.ofReal (x r ^ Q) := by
    intro r
    calc a r ^ Q ≤ (ENNReal.ofReal (c * x r)) ^ Q :=
          ENNReal.rpow_le_rpow (hax r) hQ.le
      _ = ENNReal.ofReal ((c * x r) ^ Q) := ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg hc (hx0 r)) hQ.le
      _ = ENNReal.ofReal (c ^ Q) * ENNReal.ofReal (x r ^ Q) := by
          rw [Real.mul_rpow hc (hx0 r), ENNReal.ofReal_mul (Real.rpow_nonneg hc _)]
  have hsum2 : ∑' r, a r ^ Q ≤ ENNReal.ofReal (c ^ Q * D) := by
    calc ∑' r, a r ^ Q ≤ ∑' r, ENNReal.ofReal (c ^ Q) * ENNReal.ofReal (x r ^ Q) :=
          ENNReal.tsum_le_tsum hpow
      _ = ENNReal.ofReal (c ^ Q) * ∑' r, ENNReal.ofReal (x r ^ Q) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (c ^ Q) * ENNReal.ofReal D := mul_le_mul_of_nonneg_left hsum (zero_le _)
      _ = ENNReal.ofReal (c ^ Q * D) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hc _)]
  calc (∑' r, a r ^ Q) ^ Q⁻¹ ≤ (ENNReal.ofReal (c ^ Q * D)) ^ Q⁻¹ :=
        ENNReal.rpow_le_rpow hsum2 (inv_nonneg.mpr hQ.le)
    _ = ENNReal.ofReal ((c ^ Q * D) ^ Q⁻¹) := ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (Real.rpow_nonneg hc _) hD) (inv_nonneg.mpr hQ.le)
    _ = ENNReal.ofReal (c * D ^ Q⁻¹) := by
        congr 1
        rw [Real.mul_rpow (Real.rpow_nonneg hc _) hD, ← Real.rpow_mul hc,
          mul_inv_cancel₀ hQ.ne', Real.rpow_one]

/-! ## Termo `x_r = u^s min{1, u^{-2}}` com `u = 2^r t` -/

/-- Termo adimensional da série de Besov, com `u = 2^r t`. -/
noncomputable def xr (s t : ℝ) (r : ℕ) : ℝ := ((2 : ℝ) ^ r * t) ^ s * min 1 (((2 : ℝ) ^ r * t)⁻¹ ^ 2)

lemma pow_wt_eq {s t : ℝ} (ht : 0 < t) (r : ℕ) :
    (2 : ℝ) ^ ((r : ℝ) * s) * min 1 ((1 / (2 : ℝ) ^ r / t) ^ 2) = t ^ (-s) * xr s t r := by
  unfold xr
  have h1 : ((2 : ℝ) ^ r * t) ^ s = (2 : ℝ) ^ ((r : ℝ) * s) * t ^ s := by
    rw [Real.mul_rpow (by positivity) ht.le, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
  have h2 : (1 / (2 : ℝ) ^ r / t) = ((2 : ℝ) ^ r * t)⁻¹ := by
    field_simp
  rw [h1, h2, Real.rpow_neg ht.le]
  have hts : t ^ s ≠ 0 := (Real.rpow_pos_of_pos ht s).ne'
  field_simp

lemma xr_low_eq {s t : ℝ} {n r : ℕ} (hr : r ≤ n) (hn : (2 : ℝ) ^ n * t ≤ 1) (ht : 0 < t) :
    xr s t r = ((2 : ℝ) ^ r * t) ^ s := by
  unfold xr
  have hu : (2 : ℝ) ^ r * t ≤ 1 := by
    have : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hr
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) r]
  have hinv : 1 ≤ ((2 : ℝ) ^ r * t)⁻¹ := one_le_inv_iff₀.mpr ⟨by positivity, hu⟩
  have hge : 1 ≤ ((2 : ℝ) ^ r * t)⁻¹ ^ 2 := one_le_pow₀ hinv
  rw [min_eq_left hge, mul_one]

lemma xr_high_eq {s t : ℝ} {n r : ℕ} (hr : n < r) (hn1 : 1 < (2 : ℝ) ^ (n + 1) * t) (ht : 0 < t) :
    xr s t r = ((2 : ℝ) ^ r * t) ^ (s - 2) := by
  unfold xr
  have hu1 : 1 ≤ (2 : ℝ) ^ r * t := by
    have : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) r]
  have hinv : ((2 : ℝ) ^ r * t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
  have hle : ((2 : ℝ) ^ r * t)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hinv
  rw [min_eq_right hle]
  have hpos : 0 < (2 : ℝ) ^ r * t := by positivity
  rw [show ((2 : ℝ) ^ r * t)⁻¹ ^ 2 = ((2 : ℝ) ^ r * t) ^ (-2 : ℝ) by
    rw [Real.rpow_neg hpos.le, Real.rpow_two, inv_pow]]
  rw [← Real.rpow_add hpos, sub_eq_add_neg]

/-- Cota de potência, baixa frequência: `x_r^Q ≤ α^{n-r}` com `α = 2^{-sQ}`. -/
lemma xr_low_pow {s t Q : ℝ} (hs : 0 < s) (hQ : 0 < Q) {n r : ℕ} (hr : r ≤ n)
    (hn : (2 : ℝ) ^ n * t ≤ 1) (ht : 0 < t) :
    xr s t r ^ Q ≤ ((2 : ℝ) ^ (-(s * Q))) ^ (n - r) := by
  rw [xr_low_eq hr hn ht]
  have hpos : 0 < (2 : ℝ) ^ r * t := by positivity
  have hk : (2 : ℝ) ^ r * t ≤ ((2 : ℝ) ^ (n - r))⁻¹ := by
    have e : (2 : ℝ) ^ n = (2 : ℝ) ^ r * (2 : ℝ) ^ (n - r) := by
      rw [← pow_add]; congr 1; omega
    rw [e] at hn
    have hv : (0 : ℝ) < (2 : ℝ) ^ (n - r) := by positivity
    have hmul : (2 : ℝ) ^ r * t * (2 : ℝ) ^ (n - r) ≤ 1 := by
      linarith [show (2 : ℝ) ^ r * t * (2 : ℝ) ^ (n - r) = (2 : ℝ) ^ r * (2 : ℝ) ^ (n - r) * t by ring]
    calc (2 : ℝ) ^ r * t = ((2 : ℝ) ^ r * t * (2 : ℝ) ^ (n - r)) * ((2 : ℝ) ^ (n - r))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hv.ne', mul_one]
      _ ≤ 1 * ((2 : ℝ) ^ (n - r))⁻¹ := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hv.le)
      _ = ((2 : ℝ) ^ (n - r))⁻¹ := one_mul _
  rw [← Real.rpow_mul hpos.le]
  have hsQ : 0 ≤ s * Q := (mul_pos hs hQ).le
  have e1 : ((2 : ℝ) ^ (n - r)) ^ (s * Q) = (2 : ℝ) ^ (((n - r : ℕ) : ℝ) * (s * Q)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
  have e2 : ((2 : ℝ) ^ (-(s * Q))) ^ (n - r) = (2 : ℝ) ^ (-(s * Q) * ((n - r : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
  calc ((2 : ℝ) ^ r * t) ^ (s * Q) ≤ (((2 : ℝ) ^ (n - r))⁻¹) ^ (s * Q) :=
        Real.rpow_le_rpow hpos.le hk hsQ
    _ = (((2 : ℝ) ^ (n - r)) ^ (s * Q))⁻¹ := Real.inv_rpow (by positivity) _
    _ = ((2 : ℝ) ^ (((n - r : ℕ) : ℝ) * (s * Q)))⁻¹ := by rw [e1]
    _ = (2 : ℝ) ^ (-(s * Q) * ((n - r : ℕ) : ℝ)) := by
        rw [← Real.rpow_neg zero_le_two]; congr 1; ring
    _ = ((2 : ℝ) ^ (-(s * Q))) ^ (n - r) := e2.symm

lemma xr_nonneg (s t : ℝ) (r : ℕ) (ht : 0 < t) : 0 ≤ xr s t r := by
  unfold xr
  have hu : 0 < (2 : ℝ) ^ r * t := by positivity
  exact mul_nonneg (Real.rpow_nonneg hu.le _) (le_min zero_le_one (by positivity))

/-- Cota de potência, alta frequência: `x_r^Q ≤ β^{r-n-1}` com `β = 2^{(s-2)Q}`. -/
lemma xr_high_pow {s t Q : ℝ} (hQ : 0 < Q) {n r : ℕ} (hr : n < r)
    (hn1 : 1 < (2 : ℝ) ^ (n + 1) * t) (ht : 0 < t) (hs2 : s < 2) (hs : 0 < s) :
    xr s t r ^ Q ≤ ((2 : ℝ) ^ ((s - 2) * Q)) ^ (r - n - 1) := by
  rw [xr_high_eq hr hn1 ht, ← Real.rpow_mul (by positivity)]
  have hm : (2 : ℝ) ^ (r - n - 1) ≤ (2 : ℝ) ^ r * t := by
    have e : r = (r - n - 1) + (n + 1) := by omega
    have e2 : (2 : ℝ) ^ r * t = (2 : ℝ) ^ (r - n - 1) * ((2 : ℝ) ^ (n + 1) * t) := by
      conv_lhs => rw [e]
      rw [pow_add]; ring
    rw [e2]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (r - n - 1)]
  have hexp : (s - 2) * Q ≤ 0 := by nlinarith
  have hbase : 0 < (2 : ℝ) ^ (r - n - 1) := by positivity
  calc ((2 : ℝ) ^ r * t) ^ ((s - 2) * Q) ≤ ((2 : ℝ) ^ (r - n - 1)) ^ ((s - 2) * Q) :=
        Real.rpow_le_rpow_of_nonpos hbase hm hexp
    _ = ((2 : ℝ) ^ ((s - 2) * Q)) ^ (r - n - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_natCast,
          ← Real.rpow_mul zero_le_two, mul_comm]

/-- Termo de `ℓ^Q`: `x_r^Q` é dominado pelas duas séries geométricas, para `t ≤ 1` e `n` tal que
`2^n t ≤ 1 < 2^{n+1} t`. -/
lemma xr_split {s t Q : ℝ} (hs : 0 < s) (hs2 : s < 2) (hQ : 0 < Q) (ht : 0 < t) {n : ℕ}
    (hn : (2 : ℝ) ^ n * t ≤ 1) (hn1 : 1 < (2 : ℝ) ^ (n + 1) * t) (r : ℕ) :
    0 ≤ xr s t r ^ Q ∧ xr s t r ^ Q ≤
      (if r ≤ n then ((2 : ℝ) ^ (-(s * Q))) ^ (n - r) else 0) +
      (if n < r then ((2 : ℝ) ^ ((s - 2) * Q)) ^ (r - n - 1) else 0) := by
  refine ⟨Real.rpow_nonneg (xr_nonneg s t r ht) _, ?_⟩
  by_cases hr : r ≤ n
  · rw [if_pos hr, if_neg (by omega : ¬ n < r), add_zero]
    exact xr_low_pow hs hQ hr hn ht
  · rw [if_neg hr, if_pos (by omega : n < r), zero_add]
    exact xr_high_pow hQ (by omega) hn1 ht hs2 hs

lemma xr_le_one {s t : ℝ} (hs0 : 0 ≤ s) (hs2 : s < 2) (ht : 0 < t) (r : ℕ) : xr s t r ≤ 1 := by
  unfold xr
  have hu : 0 < (2 : ℝ) ^ r * t := by positivity
  by_cases h1 : (2 : ℝ) ^ r * t ≤ 1
  · have hs : ((2 : ℝ) ^ r * t) ^ s ≤ 1 := Real.rpow_le_one hu.le h1 hs0
    have hm : min 1 (((2 : ℝ) ^ r * t)⁻¹ ^ 2) ≤ 1 := min_le_left _ _
    have hnn : 0 ≤ min 1 (((2 : ℝ) ^ r * t)⁻¹ ^ 2) := le_min zero_le_one (by positivity)
    calc ((2 : ℝ) ^ r * t) ^ s * min 1 (((2 : ℝ) ^ r * t)⁻¹ ^ 2) ≤ 1 * 1 :=
          mul_le_mul hs hm hnn zero_le_one
      _ = 1 := one_mul 1
  · have hu1 : 1 ≤ (2 : ℝ) ^ r * t := (not_le.mp h1).le
    have hinv : ((2 : ℝ) ^ r * t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
    have hle : ((2 : ℝ) ^ r * t)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hinv
    rw [min_eq_right hle, show ((2 : ℝ) ^ r * t)⁻¹ ^ 2 = ((2 : ℝ) ^ r * t) ^ (-2 : ℝ) by
      rw [Real.rpow_neg hu.le, Real.rpow_two, inv_pow], ← Real.rpow_add hu]
    exact Real.rpow_le_one_of_one_le_of_nonpos hu1 (by linarith)

/-- Cota da norma de Besov da função-teste, com constante independente de `a`, `x₀` e `t ∈ (0,1]`. -/
theorem besovNorm_bumpS_le {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hq0 : 0 < q)
    (hs : 0 < s) (hs2 : s < 2) {φ : ℝ → ℝ}
    (hφ0 : ∀ z, z ∉ Ioo (0 : ℝ) 1 → φ z = 0) {C0 M : ℝ} (hC0 : ∀ z, |φ z| ≤ C0)
    (hC00 : 0 ≤ C0) (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    (hM : ∀ z, |deriv (deriv φ) z| ≤ M) (hM0 : 0 ≤ M) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ a x0 t : ℝ, 0 < t → t ≤ 1 →
      besovNorm p s q (bumpS φ a x0 t) ≤ ENNReal.ofReal (Λ * |a| * t ^ (p.toReal⁻¹ - s)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set K := max (4 * C0) M with hKdef
  have hK0 : 0 ≤ K := le_trans (by linarith) (le_max_left _ _)
  have hr1 : 0 ≤ p.toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have h3 : 0 ≤ (3 : ℝ) ^ p.toReal⁻¹ := by positivity
  set Qr := q.toReal with hQr
  have hQ0 : 0 ≤ Qr := ENNReal.toReal_nonneg
  have hα1 : (2 : ℝ) ^ (-(s * Qr)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
  have hβ1 : (2 : ℝ) ^ ((s - 2) * Qr) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
  set D : ℝ := 1 / (1 - (2 : ℝ) ^ (-(s * Qr))) + 1 / (1 - (2 : ℝ) ^ ((s - 2) * Qr)) with hD
  have hD0 : 0 ≤ D := by
    have h1 : 0 ≤ 1 / (1 - (2 : ℝ) ^ (-(s * Qr))) := div_nonneg zero_le_one (by linarith)
    have h2 : 0 ≤ 1 / (1 - (2 : ℝ) ^ ((s - 2) * Qr)) := div_nonneg zero_le_one (by linarith)
    linarith
  set Λ : ℝ := C0 + K * (3 : ℝ) ^ p.toReal⁻¹ * (1 + D ^ Qr⁻¹) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have hD' : 0 ≤ D ^ Qr⁻¹ := Real.rpow_nonneg hD0 _
    have : 0 ≤ K * (3 : ℝ) ^ p.toReal⁻¹ * (1 + D ^ Qr⁻¹) :=
      mul_nonneg (mul_nonneg hK0 h3) (by linarith)
    linarith
  refine ⟨Λ, hΛ0, fun a x0 t ht ht1 => ?_⟩
  have habs : 0 ≤ |a| := abs_nonneg a
  set r1 := p.toReal⁻¹ with hr1def
  -- decomposição de `t^{r1}`
  have htpow : t ^ r1 = t ^ (r1 - s) * t ^ s := by
    rw [← Real.rpow_add ht]; congr 1; ring
  have hts : t ^ s ≤ 1 := Real.rpow_le_one ht.le ht1 hs.le
  have hT0 : 0 ≤ t ^ (r1 - s) := Real.rpow_nonneg ht.le _
  -- parte `L^p`
  have hL : eLpNorm (bumpS φ a x0 t) p FormalizacaoLp.vol01 ≤
      ENNReal.ofReal (|a| * C0 * t ^ (r1 - s)) := by
    refine (eLpNorm_bumpS_le hp0 hpt hφ0 hC0 hC00 ht).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [htpow]
    have : 0 ≤ |a| * C0 := mul_nonneg habs hC00
    calc |a| * C0 * (t ^ (r1 - s) * t ^ s) ≤ |a| * C0 * (t ^ (r1 - s) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hts hT0) this
      _ = |a| * C0 * t ^ (r1 - s) := by ring
  -- termo de `κ`
  set κ : ℝ := K * |a| * (3 * t) ^ r1 * t ^ (-s) with hκ
  have hκeq : κ = K * |a| * (3 : ℝ) ^ r1 * t ^ (r1 - s) := by
    have e : t ^ (r1 - s) = t ^ r1 * t ^ (-s) := by
      rw [← Real.rpow_add ht, sub_eq_add_neg]
    rw [hκ, Real.mul_rpow (by norm_num) ht.le, e]
    ring
  have hκ0 : 0 ≤ κ := by
    rw [hκeq]; positivity
  -- sequência de Besov dominada por `κ x_r`
  have hn_exists : ∃ n : ℕ, (2 : ℝ) ^ n ≤ 1 / t ∧ 1 / t < (2 : ℝ) ^ (n + 1) := by
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ 1 / t by
      rw [le_div_iff₀ ht]; linarith) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn1, hn2⟩
  obtain ⟨n, hna, hnb⟩ := hn_exists
  have hn : (2 : ℝ) ^ n * t ≤ 1 := (le_div_iff₀ ht).mp hna
  have hn1 : 1 < (2 : ℝ) ^ (n + 1) * t := (div_lt_iff₀ ht).mp hnb
  have hseq : ∀ r : ℕ, besovSeq p s (bumpS φ a x0 t) r ≤ ENNReal.ofReal (κ * xr s t r) := by
    intro r
    unfold besovSeq
    have hw := wtP_bumpS_le (a := a) (x0 := x0) hp0 hpt hφ0 hC0 hC00 hφ hφ' hM hM0 ht (1 / (2 : ℝ) ^ r)
    calc ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) * wtP p (1 / (2 : ℝ) ^ r) (bumpS φ a x0 t)
        ≤ ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
          ENNReal.ofReal (K * |a| * (3 * t) ^ r1 * min 1 ((1 / (2 : ℝ) ^ r / t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hw (zero_le _)
      _ = ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s) *
          (K * |a| * (3 * t) ^ r1 * min 1 ((1 / (2 : ℝ) ^ r / t) ^ 2))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (κ * xr s t r) := by
          congr 1
          have e := pow_wt_eq (s := s) ht r
          calc (2 : ℝ) ^ ((r : ℝ) * s) *
                (K * |a| * (3 * t) ^ r1 * min 1 ((1 / (2 : ℝ) ^ r / t) ^ 2))
              = (K * |a| * (3 * t) ^ r1) * ((2 : ℝ) ^ ((r : ℝ) * s) *
                  min 1 ((1 / (2 : ℝ) ^ r / t) ^ 2)) := by ring
            _ = (K * |a| * (3 * t) ^ r1) * (t ^ (-s) * xr s t r) := by rw [e]
            _ = κ * xr s t r := by rw [hκ]; ring
  have hx0 : ∀ r, 0 ≤ xr s t r := fun r => xr_nonneg s t r ht
  have hΛe : Λ * |a| * t ^ (r1 - s) =
      (C0 + K * (3 : ℝ) ^ r1 * (1 + D ^ Qr⁻¹)) * |a| * t ^ (r1 - s) := by rw [hΛ]
  have hsplitΛ : |a| * C0 * t ^ (r1 - s) + K * |a| * (3 : ℝ) ^ r1 * t ^ (r1 - s) ≤
      Λ * |a| * t ^ (r1 - s) := by
    rw [hΛe]
    have hD' : 0 ≤ D ^ Qr⁻¹ := Real.rpow_nonneg hD0 _
    have hnn : 0 ≤ K * (3 : ℝ) ^ r1 * D ^ Qr⁻¹ * |a| * t ^ (r1 - s) := by positivity
    have key : (C0 + K * (3 : ℝ) ^ r1 * (1 + D ^ Qr⁻¹)) * |a| * t ^ (r1 - s) -
        (|a| * C0 * t ^ (r1 - s) + K * (3 : ℝ) ^ r1 * |a| * t ^ (r1 - s)) =
        K * (3 : ℝ) ^ r1 * D ^ Qr⁻¹ * |a| * t ^ (r1 - s) := by ring
    linarith [key, hnn]
  by_cases hqt : q = ⊤
  · -- caso `q = ∞`: `x_r ≤ 1`
    subst hqt
    have hlq : lqNorm ⊤ (besovSeq p s (bumpS φ a x0 t)) ≤ ENNReal.ofReal κ := by
      unfold lqNorm
      rw [if_pos rfl]
      refine iSup_le fun r => (hseq r).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_of_le_one_right hκ0 (xr_le_one hs.le hs2 ht r)
    calc besovNorm p s ⊤ (bumpS φ a x0 t)
        = eLpNorm (bumpS φ a x0 t) p FormalizacaoLp.vol01 +
            lqNorm ⊤ (besovSeq p s (bumpS φ a x0 t)) := rfl
      _ ≤ ENNReal.ofReal (|a| * C0 * t ^ (r1 - s)) + ENNReal.ofReal κ := add_le_add hL hlq
      _ = ENNReal.ofReal (|a| * C0 * t ^ (r1 - s) + κ) := by
          rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg habs hC00) (Real.rpow_nonneg ht.le _)) hκ0]
      _ ≤ ENNReal.ofReal (Λ * |a| * t ^ (r1 - s)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hκeq]
          linarith [hsplitΛ]
  · -- caso `q < ∞`
    have hQpos : 0 < Qr := ENNReal.toReal_pos hq0.ne' hqt
    have hα0 : 0 ≤ (2 : ℝ) ^ (-(s * Qr)) := Real.rpow_nonneg zero_le_two _
    have hβ0 : 0 ≤ (2 : ℝ) ^ ((s - 2) * Qr) := Real.rpow_nonneg zero_le_two _
    have hα1' : (2 : ℝ) ^ (-(s * Qr)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
    have hβ1' : (2 : ℝ) ^ ((s - 2) * Qr) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
    have hsum : ∑' r, ENNReal.ofReal (xr s t r ^ Qr) ≤ ENNReal.ofReal D :=
      tsum_split_le hα0 hα1' hβ0 hβ1' n (fun r => xr s t r ^ Qr)
        (fun r => xr_split hs hs2 hQpos ht hn hn1 r)
    have hlq := lqNorm_le_of_pow_sum hq0 hqt (besovSeq p s (bumpS φ a x0 t)) hκ0
      (fun r => xr s t r) hx0 hseq hD0 hsum
    calc besovNorm p s q (bumpS φ a x0 t)
        = eLpNorm (bumpS φ a x0 t) p FormalizacaoLp.vol01 +
            lqNorm q (besovSeq p s (bumpS φ a x0 t)) := rfl
      _ ≤ ENNReal.ofReal (|a| * C0 * t ^ (r1 - s)) +
            ENNReal.ofReal (κ * D ^ Qr⁻¹) := add_le_add hL hlq
      _ = ENNReal.ofReal (|a| * C0 * t ^ (r1 - s) + κ * D ^ Qr⁻¹) := by
          rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg habs hC00) (Real.rpow_nonneg ht.le _))
            (mul_nonneg hκ0 (Real.rpow_nonneg hD0 _))]
      _ ≤ ENNReal.ofReal (Λ * |a| * t ^ (r1 - s)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hκeq, hΛe]
          have key : (C0 + K * (3 : ℝ) ^ r1 * (1 + D ^ Qr⁻¹)) * |a| * t ^ (r1 - s) -
              (|a| * C0 * t ^ (r1 - s) + K * |a| * (3 : ℝ) ^ r1 * t ^ (r1 - s) * D ^ Qr⁻¹) =
              K * (3 : ℝ) ^ r1 * |a| * t ^ (r1 - s) := by ring
          have pos : 0 ≤ K * (3 : ℝ) ^ r1 * |a| * t ^ (r1 - s) := by positivity
          linarith [key, pos]

end FormalizacaoAltura
