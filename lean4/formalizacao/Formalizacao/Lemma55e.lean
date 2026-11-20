import Formalizacao.Lemma55d

/-!
# Lema 5.5 (M6), parte (b): cota final do módulo `ω₁(G, t)` nas três regimes

Com `a = s - 1/p`, a cota `|G x - G y| ≤ C·φ(t)` para `|x-y| ≤ t`, com
`φ(t) = t^a` (`a < 1`), `φ(t) = t(1 + log(1/t))` (`a = 1`) e `φ(t) = t` (`a > 1`).
-/

open scoped ENNReal
open Filter Topology
open MeasureTheory Set FormalizacaoLp FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b FormalizacaoL55c FormalizacaoL55d

namespace FormalizacaoL55e

/-- `M_r = Λ_0 + K' Σ_{i=1}^{r} 2^{i(1-a)}`. -/
theorem Mseq_eq_sum (p s CW : ℝ) (S : ℝ≥0∞) (f : ℝ → ℝ) (r : ℕ) :
    Mseq p s CW S f r = Lam0 p CW f + Kslope p CW S *
      ∑ i ∈ Finset.range r, (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ) * (1 - (s - 1 / p))) := by
  induction r with
  | zero => simp [Mseq]
  | succ r ih =>
    rw [Finset.sum_range_succ, Mseq]
    rw [ih]
    ring

/-- `q^{r+1} = (2^{-(r+1)})^{a}`, com `q = (2^a)^{-1}`, `a = s - 1/p`. -/
theorem qr_pow_eq (p s : ℝ) (r : ℕ) :
    qr p s ^ (r + 1) = ((1 : ℝ) / (2 : ℝ) ^ (r + 1)) ^ (s - 1 / p) := by
  unfold qr
  rw [inv_pow, Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
    ← Real.rpow_natCast ((2 : ℝ) ^ (s - 1 / p)) (r + 1), ← Real.rpow_natCast (2 : ℝ) (r + 1),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
  simp [one_div]

/-- Escolha de `r`: `t ≤ 1/2^{r+1} < 2t`. -/
theorem choose_r {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    ∃ r : ℕ, t ≤ 1 / (2 : ℝ) ^ (r + 1) ∧ 1 / (2 : ℝ) ^ (r + 1) < 2 * t := by
  classical
  have hex : ∃ n : ℕ, 1 / (2 : ℝ) ^ (n + 2) < t := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    have h : (1 : ℝ) / 2 ^ (n + 2) ≤ (1 / 2) ^ n := by
      rw [div_pow, one_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    exact h
  set r := Nat.find hex with hr
  have hP : 1 / (2 : ℝ) ^ (r + 2) < t := Nat.find_spec hex
  refine ⟨r, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]; norm_num; linarith
    · obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hnot : ¬ (1 / (2 : ℝ) ^ (m + 2) < t) := Nat.find_min hex (by omega)
      push_neg at hnot
      have : (2 : ℝ) ^ (r + 1) = (2 : ℝ) ^ (m + 2) := by rw [hm]
      rw [this]
      exact hnot
  · have h2 : 1 / (2 : ℝ) ^ (r + 1) = 2 * (1 / (2 : ℝ) ^ (r + 2)) := by
      have e : (2 : ℝ) ^ (r + 2) = 2 * (2 : ℝ) ^ (r + 1) := by ring
      rw [e]
      field_simp
    rw [h2]
    linarith

/-- Cota comum, para `x ≤ y`. -/
theorem Glim_step_ord {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (r : ℕ) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) (hd : y - x ≤ 1 / (2 : ℝ) ^ (r + 1)) :
    |Glim f x - Glim f y| ≤
      2 * (Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s)) + Mseq p s CW S f r * (y - x) := by
  have hA := Glim_sub_le hp hW hCW hf hfi hfin hS hbS hs r hx
  have hB := Glim_sub_le hp hW hCW hf hfi hfin hS hbS hs r hy
  have hL := F_lip hp hW hCW hf hfi hfin hS hbS hs r hx hy hxy hd
  have hF : |FormalizacaoL55c.F f r x - FormalizacaoL55c.F f r y| ≤ Mseq p s CW S f r * (y - x) := by
    rw [abs_sub_comm]; exact hL
  have hsplit : Glim f x - Glim f y =
      (Glim f x - FormalizacaoL55c.F f r x + (FormalizacaoL55c.F f r x - FormalizacaoL55c.F f r y)) -
        (Glim f y - FormalizacaoL55c.F f r y) := by ring
  have h1 := abs_sub (Glim f x - FormalizacaoL55c.F f r x + (FormalizacaoL55c.F f r x - FormalizacaoL55c.F f r y))
    (Glim f y - FormalizacaoL55c.F f r y)
  have h2 := abs_add_le (Glim f x - FormalizacaoL55c.F f r x) (FormalizacaoL55c.F f r x - FormalizacaoL55c.F f r y)
  rw [hsplit]
  linarith

theorem Glim_step {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (r : ℕ) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hd : |x - y| ≤ 1 / (2 : ℝ) ^ (r + 1)) :
    |Glim f x - Glim f y| ≤
      2 * (Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s)) + Mseq p s CW S f r * |x - y| := by
  rcases le_total x y with hxy | hxy
  · have hyx : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [hyx] at hd ⊢
    exact Glim_step_ord hp hW hCW hf hfi hfin hS hbS hs r hx hy hxy hd
  · have hyx : |x - y| = x - y := abs_of_nonneg (by linarith)
    have := Glim_step_ord hp hW hCW hf hfi hfin hS hbS hs r hy hx hxy (by rw [← hyx]; exact hd)
    rw [abs_sub_comm (Glim f x) (Glim f y), hyx]
    exact this

/-- Núcleo comum: para `t ∈ (0,1/2]`, `|x-y| ≤ t`, existe `r` com `t ≤ 2^{-(r+1)}` e
`|G x - G y| ≤ C_q (2t)^a + M_r t`, com `C_q = 2 K_c/(1-q)` e `a = s - 1/p`. -/
theorem modulus_core {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : |x - y| ≤ t) :
    ∃ r : ℕ, t ≤ 1 / (2 : ℝ) ^ (r + 1) ∧
      |Glim f x - Glim f y| ≤
        2 * Kc p CW S / (1 - qr p s) * (2 * t) ^ (s - 1 / p) + Mseq p s CW S f r * t := by
  obtain ⟨r, hr1, hr2⟩ := choose_r ht ht2
  refine ⟨r, hr1, ?_⟩
  have hstep := Glim_step hp hW hCW hf hfi hfin hS hbS hs r hx hy (le_trans hxy hr1)
  have hM := Mseq_nonneg (p := p) (s := s) (CW := CW) f S
    (by unfold Lam0; positivity) (by unfold Kslope; positivity) r
  have hq1 := qr_lt_one (p := p) hs
  have hq0 := qr_nonneg p s
  have hKc := Kc_nonneg (p := p) hCW S
  have hpowle : qr p s ^ (r + 1) ≤ (2 * t) ^ (s - 1 / p) := by
    rw [qr_pow_eq]
    apply Real.rpow_le_rpow (by positivity) hr2.le
    have : (0 : ℝ) < 1 / (2 : ℝ) ^ (r + 1) := by positivity
    linarith
  have hsa : 0 ≤ s - 1 / p := by linarith
  have hfrac : 0 < 1 - qr p s := by linarith
  have h1 : 2 * (Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s)) ≤
      2 * Kc p CW S / (1 - qr p s) * (2 * t) ^ (s - 1 / p) := by
    have e : 2 * (Kc p CW S * qr p s ^ (r + 1) / (1 - qr p s)) =
        2 * Kc p CW S / (1 - qr p s) * qr p s ^ (r + 1) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left hpowle
    apply div_nonneg (by positivity) hfrac.le
  have h2 : Mseq p s CW S f r * |x - y| ≤ Mseq p s CW S f r * t :=
    mul_le_mul_of_nonneg_left hxy hM
  linarith

/-- `2^{b(r+1)} t ≤ t^{1-b}` quando `t ≤ 2^{-(r+1)}`, `b ≥ 0`. -/
theorem two_pow_mul_le {t b : ℝ} {r : ℕ} (ht : 0 < t) (hb : 0 ≤ b) (hr : t ≤ 1 / (2 : ℝ) ^ (r + 1)) :
    (2 : ℝ) ^ (b * ((r + 1 : ℕ) : ℝ)) * t ≤ t ^ (1 - b) := by
  have h1 : (2 : ℝ) ^ (b * ((r + 1 : ℕ) : ℝ)) = ((2 : ℝ) ^ (r + 1)) ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hle : (2 : ℝ) ^ (r + 1) ≤ 1 / t := by
    have hm : t * (2 : ℝ) ^ (r + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (r + 1))
      rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
    rw [le_div_iff₀ ht]
    linarith [mul_comm t ((2 : ℝ) ^ (r + 1))]
  have h2 : ((2 : ℝ) ^ (r + 1)) ^ b ≤ (1 / t) ^ b :=
    Real.rpow_le_rpow (by positivity) hle hb
  rw [h1]
  calc ((2 : ℝ) ^ (r + 1)) ^ b * t ≤ (1 / t) ^ b * t := mul_le_mul_of_nonneg_right h2 ht.le
    _ = t ^ (1 - b) := by
        rw [Real.div_rpow zero_le_one ht.le, Real.one_rpow, Real.rpow_sub ht, Real.rpow_one]
        field_simp

/-- Soma geométrica crescente: `Σ_{i<r} X^{i+1} ≤ X^{r+1}/(X-1)` para `X > 1`. -/
theorem geom_sum_succ_le {X : ℝ} (hX : 1 < X) (r : ℕ) :
    ∑ i ∈ Finset.range r, X ^ (i + 1) ≤ X ^ (r + 1) / (X - 1) := by
  have hne : X ≠ 1 := ne_of_gt hX
  have h : ∑ i ∈ Finset.range r, X ^ (i + 1) = X * ∑ i ∈ Finset.range r, X ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h, geom_sum_eq hne]
  have hX1 : 0 < X - 1 := by linarith
  have : X * ((X ^ r - 1) / (X - 1)) ≤ X ^ (r + 1) / (X - 1) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hX1.le
    rw [pow_succ]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < X) r]
  exact this

/-- `2^{n b} = (2^b)^n`. -/
theorem two_pow_nat_mul (b : ℝ) (n : ℕ) : (2 : ℝ) ^ ((n : ℝ) * b) = ((2 : ℝ) ^ b) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

/-- **Regime `s - 1/p < 1`:** `|G x - G y| ≤ C t^{s-1/p}`. -/
theorem modulus_lt1 {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (ha : s - 1 / p < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x y : ℝ, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      |x - y| ≤ t → |Glim f x - Glim f y| ≤ C * t ^ (s - 1 / p) := by
  set a : ℝ := s - 1 / p with ha_def
  set b : ℝ := 1 - a with hb_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hb0 : 0 < b := by rw [hb_def]; linarith
  set X : ℝ := (2 : ℝ) ^ b with hX_def
  have hX1 : 1 < X := Real.one_lt_rpow (by norm_num) hb0
  have hKs : 0 ≤ Kslope p CW S := by unfold Kslope; positivity
  have hLam : 0 ≤ Lam0 p CW f := by unfold Lam0; positivity
  have hA : 0 ≤ 2 * Kc p CW S / (1 - qr p s) := by
    have hq1 := qr_lt_one (p := p) hs
    have : 0 < 1 - qr p s := by linarith
    exact div_nonneg (by have := Kc_nonneg (p := p) hCW S; linarith) this.le
  refine ⟨2 * (2 * Kc p CW S / (1 - qr p s)) + Lam0 p CW f + Kslope p CW S / (X - 1), by
    have : 0 < X - 1 := by linarith
    have := div_nonneg hKs this.le
    linarith, ?_⟩
  intro t ht ht2 x y hx hy hxy
  obtain ⟨r, hr1, hcore⟩ := modulus_core hp hW hCW hf hfi hfin hS hbS hs ht ht2 hx hy hxy
  -- termo do `q`: `(2t)^a ≤ 2 t^a`
  have hq_term : 2 * Kc p CW S / (1 - qr p s) * (2 * t) ^ a ≤
      2 * (2 * Kc p CW S / (1 - qr p s)) * t ^ a := by
    rw [Real.mul_rpow (by norm_num) ht.le]
    have h2a : (2 : ℝ) ^ a ≤ 2 := by
      calc (2 : ℝ) ^ a ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha.le
        _ = 2 := Real.rpow_one 2
    have ht_a : 0 ≤ t ^ a := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2a ht_a, hA]
  -- termo de Λ_0: `t ≤ t^a`
  have hlin : t ≤ t ^ a := by
    have := Real.rpow_le_rpow_of_exponent_ge ht (by linarith) ha.le
    simpa using this
  -- soma das inclinações
  have hsum : Mseq p s CW S f r * t ≤ Lam0 p CW f * t ^ a +
      Kslope p CW S / (X - 1) * t ^ a := by
    rw [Mseq_eq_sum]
    have hexp : ∀ i : ℕ, (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ) * (1 - (s - 1 / p))) = X ^ (i + 1) := by
      intro i
      rw [← ha_def, ← hb_def, hX_def, two_pow_nat_mul]
    simp only [hexp]
    have hgeom := geom_sum_succ_le hX1 r
    have hX2 : (2 : ℝ) ^ (b * ((r + 1 : ℕ) : ℝ)) = X ^ (r + 1) := by
      rw [hX_def, ← two_pow_nat_mul]
      ring_nf
    have htb := two_pow_mul_le ht hb0.le (r := r) (by linarith [hr1])
    have hbt : 1 - b = a := by rw [hb_def]; ring
    rw [hbt] at htb
    have hsumbd : Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) * t ≤
        Kslope p CW S / (X - 1) * t ^ a := by
      have h1 : Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) * t ≤
          Kslope p CW S * (X ^ (r + 1) / (X - 1)) * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom hKs) ht.le
      have h2 : X ^ (r + 1) * t ≤ t ^ a := by
        rw [← hX2]; rw [hX2] at htb; rw [← hX2] at htb; linarith [htb]
      calc Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) * t
          ≤ Kslope p CW S * (X ^ (r + 1) / (X - 1)) * t := h1
        _ = Kslope p CW S / (X - 1) * (X ^ (r + 1) * t) := by ring
        _ ≤ Kslope p CW S / (X - 1) * t ^ a := by
            apply mul_le_mul_of_nonneg_left h2
            have : 0 < X - 1 := by linarith
            exact div_nonneg hKs this.le
    have hΛ : Lam0 p CW f * t ≤ Lam0 p CW f * t ^ a := mul_le_mul_of_nonneg_left hlin hLam
    have e : (Lam0 p CW f + Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1))) * t =
        Lam0 p CW f * t + Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) * t := by ring
    rw [e]
    linarith [hsumbd, hΛ]
  calc |Glim f x - Glim f y|
      ≤ 2 * Kc p CW S / (1 - qr p s) * (2 * t) ^ a + Mseq p s CW S f r * t := hcore
    _ ≤ 2 * (2 * Kc p CW S / (1 - qr p s)) * t ^ a + (Lam0 p CW f * t ^ a + Kslope p CW S / (X - 1) * t ^ a) := by
        linarith [hq_term, hsum]
    _ = (2 * (2 * Kc p CW S / (1 - qr p s)) + Lam0 p CW f + Kslope p CW S / (X - 1)) * t ^ a := by ring

/-- **Regime `s - 1/p = 1`:** `|G x - G y| ≤ C t(1 + log(1/t))`. -/
theorem modulus_eq1 {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (ha : s - 1 / p = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x y : ℝ, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      |x - y| ≤ t → |Glim f x - Glim f y| ≤ C * (t * (1 + Real.log (1 / t))) := by
  have hKs : 0 ≤ Kslope p CW S := by unfold Kslope; positivity
  have hLam : 0 ≤ Lam0 p CW f := by unfold Lam0; positivity
  have hq1 := qr_lt_one (p := p) hs
  have hA : 0 ≤ 2 * Kc p CW S / (1 - qr p s) := by
    have : 0 < 1 - qr p s := by linarith
    exact div_nonneg (by have := Kc_nonneg (p := p) hCW S; linarith) this.le
  refine ⟨2 * (2 * Kc p CW S / (1 - qr p s)) + Lam0 p CW f + 2 * Kslope p CW S, by linarith, ?_⟩
  intro t ht ht2 x y hx hy hxy
  obtain ⟨r, hr1, hcore⟩ := modulus_core hp hW hCW hf hfi hfin hS hbS hs ht ht2 hx hy hxy
  rw [ha, Real.rpow_one] at hcore
  have hL0 : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  -- `r ≤ 2 log(1/t)`
  have hle : (2 : ℝ) ^ (r + 1) ≤ 1 / t := by
    have hm : t * (2 : ℝ) ^ (r + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hr1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (r + 1))
      rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
    rw [le_div_iff₀ ht]
    linarith [mul_comm t ((2 : ℝ) ^ (r + 1))]
  have hlog : ((r + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (1 / t) := by
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at this
    exact this
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hrL : (r : ℝ) ≤ 2 * Real.log (1 / t) := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have h1 : (((r + 1 : ℕ) : ℝ)) * 0.69 ≤ ((r + 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by positivity)
    push_cast at h1 hlog
    nlinarith
  -- soma das inclinações: `Σ 2^{(i+1)·0} = r`
  have hK : 0 ≤ Kslope p CW S * t := mul_nonneg hKs ht.le
  have hsum : Mseq p s CW S f r * t ≤ Lam0 p CW f * t + 2 * Kslope p CW S * t * Real.log (1 / t) := by
    rw [Mseq_eq_sum, ha]
    have hz : ∀ i : ℕ, (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ) * (1 - 1)) = 1 := by
      intro i; simp
    simp only [hz, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have h3 := mul_le_mul_of_nonneg_left hrL hK
    nlinarith [h3]
  have hL' : 0 ≤ Lam0 p CW f * t * Real.log (1 / t) := mul_nonneg (mul_nonneg hLam ht.le) hL0
  calc |Glim f x - Glim f y|
      ≤ 2 * Kc p CW S / (1 - qr p s) * (2 * t) + Mseq p s CW S f r * t := hcore
    _ ≤ (2 * (2 * Kc p CW S / (1 - qr p s)) + Lam0 p CW f + 2 * Kslope p CW S) * (t * (1 + Real.log (1 / t))) := by
        nlinarith [hsum, hL', hK, mul_nonneg hA ht.le, mul_nonneg hKs (mul_nonneg ht.le hL0)]

/-- **Regime `s - 1/p > 1`:** `|G x - G y| ≤ C t`. -/
theorem modulus_gt1 {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (ha : 1 < s - 1 / p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x y : ℝ, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      |x - y| ≤ t → |Glim f x - Glim f y| ≤ C * t := by
  set a : ℝ := s - 1 / p with ha_def
  set b : ℝ := 1 - a with hb_def
  have hb1 : b < 0 := by rw [hb_def]; linarith
  set X : ℝ := (2 : ℝ) ^ b with hX_def
  have hX0 : 0 < X := Real.rpow_pos_of_pos (by norm_num) _
  have hX1 : X < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hb1
  have hKs : 0 ≤ Kslope p CW S := by unfold Kslope; positivity
  have hLam : 0 ≤ Lam0 p CW f := by unfold Lam0; positivity
  have hq1 := qr_lt_one (p := p) hs
  have hA : 0 ≤ 2 * Kc p CW S / (1 - qr p s) := by
    have : 0 < 1 - qr p s := by linarith
    exact div_nonneg (by have := Kc_nonneg (p := p) hCW S; linarith) this.le
  have hD : 0 < 1 - X := by linarith
  refine ⟨2 * (2 * Kc p CW S / (1 - qr p s)) + Lam0 p CW f + Kslope p CW S / (1 - X), by
    have := div_nonneg hKs hD.le
    linarith, ?_⟩
  intro t ht ht2 x y hx hy hxy
  obtain ⟨r, hr1, hcore⟩ := modulus_core hp hW hCW hf hfi hfin hS hbS hs ht ht2 hx hy hxy
  have ht1 : 2 * t ≤ 1 := by linarith
  have hq_term : 2 * Kc p CW S / (1 - qr p s) * (2 * t) ^ a ≤ 2 * (2 * Kc p CW S / (1 - qr p s)) * t := by
    have h2 : (2 * t) ^ a ≤ (2 * t) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) ht1 (by linarith)
    rw [Real.rpow_one] at h2
    nlinarith [mul_le_mul_of_nonneg_left h2 hA]
  -- soma geométrica decrescente
  have hsum : Mseq p s CW S f r * t ≤ Lam0 p CW f * t + Kslope p CW S / (1 - X) * t := by
    rw [Mseq_eq_sum]
    have hexp : ∀ i : ℕ, (2 : ℝ) ^ (((i + 1 : ℕ) : ℝ) * (1 - (s - 1 / p))) = X ^ (i + 1) := by
      intro i
      rw [← ha_def, ← hb_def, hX_def, two_pow_nat_mul]
    simp only [hexp]
    have hgeo : ∑ i ∈ Finset.range r, X ^ (i + 1) ≤ 1 / (1 - X) := by
      have h1 := geom_sum_Ico_le_of_lt_one (x := X) (m := 0) (n := r) hX0.le hX1
      rw [Finset.range_eq_Ico]
      have h2 : ∑ i ∈ Finset.Ico 0 r, X ^ (i + 1) ≤ ∑ i ∈ Finset.Ico 0 r, X ^ i := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_of_le_one hX0.le hX1.le (by omega)
      simp only [pow_zero] at h1
      linarith
    have hK : 0 ≤ Kslope p CW S * t := mul_nonneg hKs ht.le
    have hΛ : 0 ≤ Lam0 p CW f * t := mul_nonneg hLam ht.le
    have hsumbd : Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) * t ≤ Kslope p CW S / (1 - X) * t := by
      have : Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) ≤ Kslope p CW S / (1 - X) := by
        have := mul_le_mul_of_nonneg_left hgeo hKs
        calc Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) ≤ Kslope p CW S * (1 / (1 - X)) := this
          _ = Kslope p CW S / (1 - X) := by ring
      exact mul_le_mul_of_nonneg_right this ht.le
    have e : (Lam0 p CW f + Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1))) * t =
        Lam0 p CW f * t + Kslope p CW S * (∑ i ∈ Finset.range r, X ^ (i + 1)) * t := by ring
    rw [e]
    linarith [hsumbd]
  calc |Glim f x - Glim f y|
      ≤ 2 * Kc p CW S / (1 - qr p s) * (2 * t) ^ a + Mseq p s CW S f r * t := hcore
    _ ≤ 2 * (2 * Kc p CW S / (1 - qr p s)) * t + (Lam0 p CW f * t + Kslope p CW S / (1 - X) * t) := by
        linarith [hq_term, hsum]
    _ = (2 * (2 * Kc p CW S / (1 - qr p s)) + Lam0 p CW f + Kslope p CW S / (1 - X)) * t := by ring

end FormalizacaoL55e
