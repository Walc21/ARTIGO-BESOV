import Formalizacao.Lemma55

/-!
# Lema 5.5 (M6), parte numérica: cotas de `v_k = Q_{2^{k+1}} f - Q_{2^k} f`

Com `S = sup_m 2^{ms} ω_p(f, 2^{-m})` (finito, por `f ∈ B^s_{p,∞}`), `s' = s - 1/p`:
`‖v_k‖_∞ ≤ K 2^{-ks'}` e `|v_k'| ≤ K' 2^{k(1-s')}` (pedaços afins da malha `2^{-(k+1)}`).
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoLp FormalizacaoGrid FormalizacaoL55

namespace FormalizacaoL55b

/-- `ω_p(f, 1/n)` como número real. -/
noncomputable def Wr (p : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f).toReal

/-- `ω_p(f, 1/n) < ∞` para `f ∈ L^p`. -/
lemma wtP_lt_top {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : Measurable f)
    (hfin : Np p f (Icc 0 1) < ⊤) (n : ℕ) :
    wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f < ⊤ :=
  lt_of_le_of_lt (wtP_le_four (ENNReal.one_le_ofReal.2 hp) _ hf)
    (ENNReal.mul_lt_top (by norm_num) hfin)

/-- `Np(Q_{2n} f - Q_n f) ≤ 18 C_W ω(1/n)` como real. -/
lemma toReal_v_le {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) :
    (Np p (fun y => Q (2 * n) f y - Q n f y) (Icc 0 1)).toReal ≤ 18 * CW * Wr p f n := by
  have hR : 18 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      (wtP_lt_top hp hf hfin n).ne
  calc (Np p (fun y => Q (2 * n) f y - Q n f y) (Icc 0 1)).toReal
      ≤ (18 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f).toReal :=
        ENNReal.toReal_mono hR (v_norm_le hp hW hCW hn hf hfi hfin)
    _ = 18 * CW * Wr p f n := by
        unfold Wr
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCW]
        norm_num

/-- Cota sup da diferença de escalas. -/
theorem sup_diff_le {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |Q (2 * n) f x - Q n f x| ≤
      8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p)) * (18 * CW * Wr p f n) := by
  have hv : ∀ j, j < 2 * n → ∃ α β : ℝ, ∀ x ∈ cell (2 * n) j,
      (fun y => Q (2 * n) f y - Q n f y) x = α + β * x := fun j hj =>
    Q_diff_affine_fine (by omega) hj f
  have hvfin : Np p (fun y => Q (2 * n) f y - Q n f y) (Icc 0 1) < ⊤ := by
    refine lt_of_le_of_lt (v_norm_le hp hW hCW hn hf hfi hfin) ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
      (wtP_lt_top hp hf hfin n)
  have hs := sup_le_of_affine_cells (N := 2 * n) hp (by omega) hv hvfin hx
  have hb := toReal_v_le hp hW hCW hn hf hfi hfin
  have hc : (0 : ℝ) ≤ 8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p)) := by positivity
  calc |Q (2 * n) f x - Q n f x| ≤ 8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p)) *
        (Np p (fun y => Q (2 * n) f y - Q n f y) (Icc 0 1)).toReal := hs
    _ ≤ 8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p)) * (18 * CW * Wr p f n) :=
        mul_le_mul_of_nonneg_left hb hc

/-- Cota de inclinação da diferença de escalas, em cada célula fina. -/
theorem slope_diff_le {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {j : ℕ} (hj : j < 2 * n) :
    ∃ β : ℝ, |β| ≤ 8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p) - 1) * (18 * CW * Wr p f n) ∧
      ∃ α : ℝ, ∀ x ∈ cell (2 * n) j, Q (2 * n) f x - Q n f x = α + β * x := by
  have hv : ∀ i, i < 2 * n → ∃ α β : ℝ, ∀ x ∈ cell (2 * n) i,
      (fun y => Q (2 * n) f y - Q n f y) x = α + β * x := fun i hi =>
    Q_diff_affine_fine (by omega) hi f
  have hvfin : Np p (fun y => Q (2 * n) f y - Q n f y) (Icc 0 1) < ⊤ := by
    refine lt_of_le_of_lt (v_norm_le hp hW hCW hn hf hfi hfin) ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
      (wtP_lt_top hp hf hfin n)
  obtain ⟨β, hβ, α, hab⟩ := slope_le_of_affine_cells hp (by omega) hv hvfin hj
  refine ⟨β, ?_, α, hab⟩
  have hb := toReal_v_le hp hW hCW hn hf hfi hfin
  have hc : (0 : ℝ) ≤ 8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p) - 1) := by positivity
  calc |β| ≤ 8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p) - 1) *
        (Np p (fun y => Q (2 * n) f y - Q n f y) (Icc 0 1)).toReal := hβ
    _ ≤ 8 * (1 / ((2 * n : ℕ) : ℝ)) ^ (-(1 / p) - 1) * (18 * CW * Wr p f n) :=
        mul_le_mul_of_nonneg_left hb hc

/-- Pela hipótese de Besov em sup: `ω_p(f, 2^{-m}) ≤ S · 2^{-ms}`, com `S` o supremo. -/
theorem Wr_le_of_besov {p s : ℝ} {f : ℝ → ℝ} {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S) (m : ℕ) :
    Wr p f (2 ^ m) ≤ S.toReal * ((2 : ℝ) ^ ((m : ℝ) * s))⁻¹ := by
  have h := hbS m
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((m : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 := ENNReal.toReal_mono hS.ne h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos.le] at h2
  unfold Wr
  rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- `(1/2^{k+1})^{-c} = 2^{(k+1)c}`. -/
lemma two_pow_neg_rpow (k : ℕ) (c : ℝ) :
    ((1 : ℝ) / ((2 : ℝ) ^ (k + 1))) ^ (-c) = (2 : ℝ) ^ (((k : ℝ) + 1) * c) := by
  rw [one_div, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  push_cast
  ring_nf

/-- **Cota sup de `v_k`**, com `s' = s - 1/p`: `|v_k| ≤ K 2^{-ks'}`, `K = 144 C_W S 2^{1/p}`. -/
theorem vk_sup_le {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x| ≤
      144 * CW * S.toReal * (2 : ℝ) ^ (1 / p) * ((2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)))⁻¹ := by
  have hn2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  have hbase := sup_diff_le hp hW hCW hn2 hf hfi hfin hx
  rw [h2k] at hbase
  have hW' := Wr_le_of_besov (p := p) (s := s) hS hbS k
  have hSnn : 0 ≤ S.toReal := ENNReal.toReal_nonneg
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  -- potências
  have hA : ((1 : ℝ) / ((2 : ℝ) ^ (k + 1))) ^ (-(1 / p)) = (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) := by
    rw [two_pow_neg_rpow]
  have hWr : (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹ =
      (2 : ℝ) ^ (1 / p) * ((2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)))⁻¹ := by
    have e1 : (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) = (2 : ℝ) ^ (1 / p) * (2 : ℝ) ^ ((k : ℝ) * (1 / p)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have e2 : (2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)) = (2 : ℝ) ^ ((k : ℝ) * s) / (2 : ℝ) ^ ((k : ℝ) * (1 / p)) := by
      rw [← Real.rpow_sub (by norm_num)]
      congr 1
      ring
    rw [e1, e2]
    have : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) * (1 / p)) := Real.rpow_pos_of_pos (by norm_num) _
    field_simp
  have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  rw [hcast, hA] at hbase
  calc |Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x|
      ≤ 8 * (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) * (18 * CW * Wr p f (2 ^ k)) := hbase
    _ ≤ 8 * (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) * (18 * CW * (S.toReal * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹)) := by
        gcongr
    _ = 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p) * ((2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)))⁻¹ := by
        have hW2 : (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹ * (144 * CW * S.toReal) =
            (2 : ℝ) ^ (1 / p) * ((2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)))⁻¹ * (144 * CW * S.toReal) := by
          rw [hWr]
        calc 8 * (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) * (18 * CW * (S.toReal * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹))
            = (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹ * (144 * CW * S.toReal) := by
              ring
          _ = (2 : ℝ) ^ (1 / p) * ((2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)))⁻¹ * (144 * CW * S.toReal) := hW2
          _ = 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p) * ((2 : ℝ) ^ ((k : ℝ) * (s - 1 / p)))⁻¹ := by
              ring

/-- **Cota de inclinação de `v_k`**: `|β_k| ≤ K' 2^{k(1-s')}`, `K' = 144 C_W S 2^{1/p+1}`. -/
theorem vk_slope_le {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hj : j < 2 ^ (k + 1)) :
    ∃ β : ℝ, |β| ≤ 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p + 1) * (2 : ℝ) ^ ((k : ℝ) * (1 - (s - 1 / p))) ∧
      ∃ α : ℝ, ∀ x ∈ cell (2 ^ (k + 1)) j, Q (2 ^ (k + 1)) f x - Q (2 ^ k) f x = α + β * x := by
  have hn2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  have hj' : j < 2 * 2 ^ k := by rw [h2k]; exact hj
  obtain ⟨β, hβ, α, hab⟩ := slope_diff_le hp hW hCW hn2 hf hfi hfin hj'
  rw [h2k] at hβ hab
  refine ⟨β, ?_, α, hab⟩
  have hW' := Wr_le_of_besov (p := p) (s := s) hS hbS k
  have hcast : ((2 * 2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  rw [h2k] at hcast
  rw [hcast] at hβ
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) * s) := Real.rpow_pos_of_pos (by norm_num) _
  have hSnn : 0 ≤ S.toReal := ENNReal.toReal_nonneg
  have hB : (1 / ((2 : ℝ) ^ (k + 1))) ^ (-(1 / p) - 1) = (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p + 1)) := by
    rw [show -(1 / p) - 1 = -(1 / p + 1) by ring, two_pow_neg_rpow]
  have hWr : (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p + 1)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹ =
      (2 : ℝ) ^ (1 / p + 1) * (2 : ℝ) ^ ((k : ℝ) * (1 - (s - 1 / p))) := by
    have e1 : (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p + 1)) =
        (2 : ℝ) ^ (1 / p + 1) * (2 : ℝ) ^ ((k : ℝ) * (1 / p + 1)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have e2 : (2 : ℝ) ^ ((k : ℝ) * (1 - (s - 1 / p))) =
        (2 : ℝ) ^ ((k : ℝ) * (1 / p + 1)) / (2 : ℝ) ^ ((k : ℝ) * s) := by
      rw [← Real.rpow_sub (by norm_num)]
      congr 1
      ring
    rw [e1, e2]
    have : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) * (1 / p + 1)) := Real.rpow_pos_of_pos (by norm_num) _
    field_simp
  rw [hB] at hβ
  calc |β| ≤ 8 * (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p + 1)) * (18 * CW * Wr p f (2 ^ k)) := hβ
    _ ≤ 8 * (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p + 1)) * (18 * CW * (S.toReal * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹)) := by
        gcongr
    _ = 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p + 1) * (2 : ℝ) ^ ((k : ℝ) * (1 - (s - 1 / p))) := by
        calc 8 * (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p + 1)) * (18 * CW * (S.toReal * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹))
            = (2 : ℝ) ^ (((k : ℝ) + 1) * (1 / p + 1)) * ((2 : ℝ) ^ ((k : ℝ) * s))⁻¹ * (144 * CW * S.toReal) := by
              ring
          _ = (2 : ℝ) ^ (1 / p + 1) * (2 : ℝ) ^ ((k : ℝ) * (1 - (s - 1 / p))) * (144 * CW * S.toReal) := by
              rw [hWr]
          _ = 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p + 1) * (2 : ℝ) ^ ((k : ℝ) * (1 - (s - 1 / p))) := by
              ring

end FormalizacaoL55b
