import Formalizacao.UnifTheorem

/-!
# Critério de somabilidade para agendas regulares (seção 6.3)

O teto conserva a comparabilidade dos pesos com `1/h`. A mudança de uma série
sobre escalas diádicas para uma série sobre todos os orçamentos usa condensação de Cauchy.
-/

open scoped ENNReal
open Set FormalizacaoLp

namespace FormalizacaoRegular

/-- Agenda com fator regular multiplicativo. -/
noncomputable def Hregular (s : ℝ) (h : ℕ → ℝ) (N : ℕ) : ℕ :=
  ⌈8 * ((N : ℝ) + 1) ^ s * h N⌉₊

/-- Peso no critério de Jackson, começando na escala `r = 1`. -/
noncomputable def scheduleWeight (s : ℝ) (H : ℕ → ℕ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) / (H (2 ^ (k + 1)) : ℝ≥0∞)

lemma lq_ofReal_iff {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) :
    lqNorm q (fun k ↦ ENNReal.ofReal (a k)) < ⊤ ↔ Summable (fun k ↦ a k ^ q.toReal) := by
  have hqR := ENNReal.toReal_pos hq.ne' hqt
  rw [lqNorm, if_neg hqt, ENNReal.rpow_lt_top_iff_of_pos (inv_pos.mpr hqR)]
  have he : (∑' k, ENNReal.ofReal (a k) ^ q.toReal) =
      ∑' k, ENNReal.ofReal (a k ^ q.toReal) :=
    tsum_congr fun k ↦ ENNReal.ofReal_rpow_of_nonneg (ha k) hqR.le
  rw [he]
  refine ⟨fun h ↦ ?_, Summable.tsum_ofReal_lt_top⟩
  unfold ENNReal.ofReal at h
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe] at h
  have he (k : ℕ) := Real.coe_toNNReal _ (Real.rpow_nonneg (ha k) q.toReal)
  simpa only [he] using h

lemma Hregular_lower {s : ℝ} (hs : 0 ≤ s) {h : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h N) :
    8 * (N : ℝ) ^ s * h N ≤ (Hregular s h N : ℝ) := by
  have hcast : (0 : ℝ) ≤ N := by positivity
  refine le_trans ?_ (Nat.le_ceil _)
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hh)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hcast (by linarith) hs) (by norm_num)

lemma Hregular_upper {s : ℝ} (hs : 0 ≤ s) {h : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h N) :
    (Hregular s h N : ℝ) ≤ (8 * (2 : ℝ) ^ s + 1) * (N : ℝ) ^ s * h N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ h N := zero_le_one.trans hh
  have hpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)
    (show (N : ℝ) + 1 ≤ 2 * N by linarith) hs
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hpow
  have hNpow : 1 ≤ (N : ℝ) ^ s := Real.one_le_rpow hNr hs
  have hprod : 1 ≤ (N : ℝ) ^ s * h N := one_le_mul_of_one_le_of_one_le hNpow hh
  calc _ ≤ 8 * ((N : ℝ) + 1) ^ s * h N + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ 8 * ((2 : ℝ) ^ s * (N : ℝ) ^ s) * h N + 1 :=
      add_le_add_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 8)) h0) 1
    _ ≤ _ := by linarith

lemma scheduleWeight_eq_ofReal (s : ℝ) (H : ℕ → ℕ) (k : ℕ)
    (hH : 0 < H (2 ^ (k + 1))) :
    scheduleWeight s H k =
      ENNReal.ofReal (((2 ^ (k + 1) : ℕ) : ℝ) ^ s / (H (2 ^ (k + 1)) : ℝ)) := by
  rw [scheduleWeight, ENNReal.ofReal_div_of_pos (by exact_mod_cast hH), ENNReal.ofReal_natCast,
    Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul (by norm_num)]

/-- Comparação de convergência sob cotas positivas nos dois sentidos. -/
lemma summable_iff_of_comparable {f g : ℕ → ℝ} {C D : ℝ}
    (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    (hfg : ∀ k, f k ≤ C * g k) (hgf : ∀ k, g k ≤ D * f k) :
    Summable f ↔ Summable g :=
  ⟨fun hs ↦ (hs.mul_left D).of_nonneg_of_le hg hgf,
    fun hs ↦ (hs.mul_left C).of_nonneg_of_le hf hfg⟩

private lemma regular_dyadic_iff {s : ℝ} (hs : 1 ≤ s) {q : ℝ≥0∞}
    (hq : 0 < q) (hqt : q ≠ ⊤) {h : ℕ → ℝ} (hh : ∀ N, 1 ≤ N → 1 ≤ h N) :
    lqNorm q (scheduleWeight s (Hregular s h)) < ⊤ ↔
      Summable (fun k : ℕ ↦ h (2 ^ (k + 1)) ^ (-q.toReal)) := by
  let a : ℕ → ℝ := fun k ↦ (((2 ^ (k + 1) : ℕ) : ℝ) ^ s) / (Hregular s h (2 ^ (k + 1)) : ℝ)
  let b : ℕ → ℝ := fun k ↦ (h (2 ^ (k + 1)))⁻¹
  let D : ℝ := 8 * (2 : ℝ) ^ s + 1
  have hq0 := ENNReal.toReal_nonneg (a := q)
  have hH (k : ℕ) : 0 < Hregular s h (2 ^ (k + 1)) := by
    have hn : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
    have hlower := Hregular_lower (zero_le_one.trans hs) hn (hh _ hn)
    have hh' : 0 < h (2 ^ (k + 1)) := zero_lt_one.trans_le (hh _ Nat.one_le_two_pow)
    have h' : (0 : ℝ) < (Hregular s h (2 ^ (k + 1)) : ℝ) :=
      lt_of_lt_of_le (by positivity) hlower
    exact_mod_cast h'
  have ha (k : ℕ) : 0 ≤ a k := by dsimp [a]; positivity
  have hb (k : ℕ) : 0 ≤ b k := inv_nonneg.mpr (zero_le_one.trans (hh _ Nat.one_le_two_pow))
  have he : scheduleWeight s (Hregular s h) = fun k ↦ ENNReal.ofReal (a k) :=
    funext fun k ↦ scheduleWeight_eq_ofReal s _ k (hH k)
  have hbpow (k : ℕ) : b k ^ q.toReal = h (2 ^ (k + 1)) ^ (-q.toReal) := by
    dsimp only [b]
    rw [Real.inv_rpow (zero_le_one.trans (hh _ Nat.one_le_two_pow)),
      Real.rpow_neg (zero_le_one.trans (hh _ Nat.one_le_two_pow))]
  rw [he, lq_ofReal_iff hq hqt ha, show (fun k : ℕ ↦ h (2 ^ (k + 1)) ^ (-q.toReal)) =
    (fun k ↦ b k ^ q.toReal) from funext fun k ↦ (hbpow k).symm]
  have h₁ (k : ℕ) : a k ≤ b k := by
    have hn : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
    have hpos : 0 < h (2 ^ (k + 1)) := zero_lt_one.trans_le (hh _ hn)
    unfold a b
    rw [← one_div, div_le_div_iff₀ (by exact_mod_cast hH k) hpos, one_mul]
    have hlow := Hregular_lower (zero_le_one.trans hs) hn (hh _ hn)
    exact le_trans (by
      have : 0 ≤ (((2 ^ (k + 1) : ℕ) : ℝ) ^ s) * h (2 ^ (k + 1)) := by positivity
      nlinarith only [this]) hlow
  have h₂ (k : ℕ) : b k ≤ D * a k := by
    have hn : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
    have hpos : 0 < h (2 ^ (k + 1)) := zero_lt_one.trans_le (hh _ hn)
    unfold a b
    rw [← one_div, ← mul_div_assoc, div_le_div_iff₀ hpos (by exact_mod_cast hH k), one_mul]
    exact Hregular_upper (zero_le_one.trans hs) hn (hh _ hn)
  apply summable_iff_of_comparable (C := 1) (D := D ^ q.toReal)
    (fun k ↦ Real.rpow_nonneg (ha k) _) (fun k ↦ Real.rpow_nonneg (hb k) _)
  · intro k
    simpa only [one_mul] using Real.rpow_le_rpow (ha k) (h₁ k) hq0
  · intro k
    have h := Real.rpow_le_rpow (hb k) (h₂ k) hq0
    rwa [Real.mul_rpow (by dsimp [D]; positivity) (ha k)] at h

/-- Proposição 6.11: critério exato para agendas com fator regular não decrescente. -/
theorem regular_schedule_criterion {s : ℝ} (hs : 1 ≤ s) {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤)
    {h : ℕ → ℝ} (hh : ∀ N, 1 ≤ N → 1 ≤ h N) (hm : MonotoneOn h (Ici 1)) :
    (lqNorm q (scheduleWeight s (Hregular s h)) < ⊤ ↔
      Summable (fun k : ℕ ↦ h (2 ^ (k + 1)) ^ (-q.toReal))) ∧
    (Summable (fun k : ℕ ↦ h (2 ^ (k + 1)) ^ (-q.toReal)) ↔
      Summable (fun k : ℕ ↦ 1 / (((k + 1 : ℕ) : ℝ) * h (k + 1) ^ q.toReal))) := by
  refine ⟨regular_dyadic_iff hs hq hqt hh, ?_⟩
  let f (N : ℕ) : ℝ := 1 / ((N : ℝ) * h N ^ q.toReal)
  have hf0 (n : ℕ) : 0 ≤ f n := by
    cases n with
    | zero => simp [f]
    | succ n =>
      have := zero_le_one.trans (hh (n + 1) (by omega))
      dsimp [f]
      positivity
  have hfm ⦃m n : ℕ⦄ (hm0 : 0 < m) (hmn : m ≤ n) : f n ≤ f m := by
    have hm' := hh m hm0
    have hn' := hh n (hm0.trans_le hmn)
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul (by exact_mod_cast hmn)
      (Real.rpow_le_rpow (zero_le_one.trans hm') (hm hm0 (hm0.trans_le hmn) hmn)
        ENNReal.toReal_nonneg) (by positivity) (by positivity)
  have he (k : ℕ) : (2 : ℝ) ^ k * f (2 ^ k) = h (2 ^ k) ^ (-q.toReal) := by
    have h₀ : 0 < h (2 ^ k) := zero_lt_one.trans_le (hh _ Nat.one_le_two_pow)
    dsimp [f]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg h₀.le]
    field_simp
  have hc := summable_condensed_iff_of_nonneg hf0 hfm
  simp_rw [he] at hc
  exact (summable_nat_add_iff 1).trans (hc.trans (summable_nat_add_iff (f := f) 1).symm)


open FormalizacaoLow FormalizacaoLq Filter

/-- Observação 6.4: com `κ = 0` e `s ≥ 1`, o peso de quantização não é somável em
`ℓ^q` para `q` finito. O teto diádico deixa o peso separado de zero. -/
theorem uniform_quantWeight_zero_not_lt_top {p s : ℝ} (hp : 1 ≤ p) (hs : 1 ≤ s)
    {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) :
    ¬ lqNorm q (quantWeight s (qexp (nuPrime p s) (hfun (kapPrime p s 0)))) < ⊤ := by
  have hν : nuPrime p s = s := by
    have hp' : 1 / p ≤ 1 := (div_le_one (by linarith)).mpr hp
    unfold nuPrime
    split_ifs with h
    · exact max_eq_right hs
    · linarith
  have hκ : kapPrime p s 0 = 0 := by unfold kapPrime; split_ifs <;> rfl
  have hh : hfun 0 = fun _ ↦ 1 := by funext N; simp [hfun]
  rw [hν, hκ, hh]
  intro h
  have hlo (k : ℕ) : ENNReal.ofReal (1 / 4) ≤ quantWeight s (qexp s (fun _ ↦ 1)) k := by
    have hQ := (qexp_spec hs (h := fun _ ↦ 1) (fun _ ↦ le_rfl) (k + 1)).2.2
    change (2 : ℝ) ^ qexp s (fun _ ↦ 1) (k + 1) ≤ 2 * (((2 : ℝ) ^ (k + 1)) ^ s * 1) at hQ
    rw [mul_one, ← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul (by norm_num)] at hQ
    rw [quantWeight, ← ENNReal.ofReal_mul (by positivity), ← div_eq_mul_one_div]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hc := (lq_mono hq hlo).trans_lt h
  have hr := (lq_ofReal_iff hq hqt (a := fun _ ↦ 1 / 4) (fun _ ↦ by norm_num)).mp hc
  have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4) q.toReal
  exact hpos.ne' (tendsto_nhds_unique tendsto_const_nhds hr.tendsto_atTop_zero)

end FormalizacaoRegular
