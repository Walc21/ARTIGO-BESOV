import Formalizacao.LqLemmas

/-!
# Agendas de altura e pesos `ℓ^q`

Para as agendas da Parte IV (`H_{s,κ}` = `Pendencias.Agenda.Hsk`, e `H̃_{s,η}` =
`Pendencias.Jackson.HtilK 0 0`), mostra-se:

* a cota inferior `8 N^{max 1 s} ≤ H(N)` (com o fator logarítmico, quando há);
* os pesos `w_k = 2^{(k+1)s} / H(2^{k+1})` pertencem a `ℓ^q`, nos casos das conjecturas:
  - `weight_geom`: se `H(N) ≥ 8 N^a` com `a > s`, então `w` é dominado por uma geométrica;
  - `weight_poly`: para `H_{s,κ}` com `s ≥ 1`, `w` é dominado por `(k+1)^{-κ}`.
-/

open scoped ENNReal

namespace FormalizacaoSched

open FormalizacaoLq

/-- Identidade de potências: `2^{ts} = (2^t)^a · (2^{s-a})^t`. -/
theorem rpow_two_identity (s a t : ℝ) :
    (2 : ℝ) ^ (t * s) = ((2 : ℝ) ^ t) ^ a * ((2 : ℝ) ^ (s - a)) ^ t := by
  rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  ring

/-- Cota inferior real para `Hsk`: `H_{s,κ}(N) ≥ 8 (N+1)^{max 1 s} log(eN)^κ`. -/
theorem Hsk_real_ge (s κ : ℝ) (N : ℕ) :
    8 * ((N : ℝ) + 1) ^ (max 1 s) * Real.log (Real.exp 1 * N) ^ κ ≤
      (Pendencias.Agenda.Hsk s κ N : ℝ) :=
  Nat.le_ceil _

/-- Cota inferior real para `HtilK 0 0`: `H̃_{s,η}(N) ≥ 8 (N+1)^{max 1 (s+η)}`. -/
theorem Htil_real_ge (s η : ℝ) (N : ℕ) :
    8 * ((N : ℝ) + 1) ^ (max 1 (s + η)) ≤ (Pendencias.Jackson.HtilK 0 0 s η N : ℝ) := by
  have hC : Pendencias.Jackson.CK 0 0 = 8 := by
    norm_num [Pendencias.Jackson.CK]
  unfold Pendencias.Jackson.HtilK
  rw [hC]
  exact Nat.le_ceil _

/-- Peso geométrico: se `H(N) ≥ 8 N^a` para `N ≥ 1` e `a > s`, então
`2^{(k+1)s}/H(2^{k+1}) ≤ (ρ/8) ρ^k`, com `ρ = 2^{s-a} < 1`. -/
theorem weight_geom (H : ℕ → ℕ) {s a : ℝ} (hsa : s < a)
    (hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ a ≤ (H N : ℝ)) (k : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) / (H (2 ^ (k + 1)) : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (s - a) / 8 * ((2 : ℝ) ^ (s - a)) ^ k) := by
  set N : ℕ := 2 ^ (k + 1) with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNr : (N : ℝ) = (2 : ℝ) ^ (((k + 1 : ℕ)) : ℝ) := by
    rw [hNdef, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNa : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNpos a
  have hHk := hH N hN1
  have hHpos : (0 : ℝ) < (H N : ℝ) := by nlinarith
  have hx : (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) = (N : ℝ) ^ a * ((2 : ℝ) ^ (s - a)) ^ (k + 1) := by
    rw [hNr, rpow_two_identity s a _]
    congr 1
    rw [← Real.rpow_natCast]
  rw [← ENNReal.ofReal_natCast (H N), ← ENNReal.ofReal_div_of_pos hHpos]
  apply ENNReal.ofReal_le_ofReal
  have hx0 : (0 : ℝ) ≤ (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) := by positivity
  calc (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) / (H N : ℝ)
      ≤ (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) / (8 * (N : ℝ) ^ a) :=
        div_le_div_of_nonneg_left hx0 (by positivity) hHk
    _ = (2 : ℝ) ^ (s - a) / 8 * ((2 : ℝ) ^ (s - a)) ^ k := by
        rw [hx, pow_succ]
        field_simp

/-- Identidade `log(e·2^{k+1}) = 1 + (k+1) log 2`. -/
theorem log_e_pow_two (k : ℕ) :
    Real.log (Real.exp 1 * ((2 ^ (k + 1) : ℕ) : ℝ)) = 1 + ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow]

/-- Peso polinomial para `H_{s,κ}` com `s ≥ 1` e `κ ≥ 0`:
`2^{(k+1)s}/H(2^{k+1}) ≤ (1/8)(log 2)^{-κ} (k+1)^{-κ}`. -/
theorem weight_poly {s κ : ℝ} (hs : 1 ≤ s) (hκ : 0 ≤ κ) (k : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) /
        (Pendencias.Agenda.Hsk s κ (2 ^ (k + 1)) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 8 * (Real.log 2) ^ (-κ) * ((k + 1 : ℕ) : ℝ) ^ (-κ)) := by
  set N : ℕ := 2 ^ (k + 1) with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNr : (N : ℝ) = (2 : ℝ) ^ (((k + 1 : ℕ)) : ℝ) := by
    rw [hNdef, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlogN : Real.log (Real.exp 1 * N) = 1 + ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [hNdef]; exact log_e_pow_two k
  set M : ℝ := ((k + 1 : ℕ) : ℝ) * Real.log 2 with hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hMpos : 0 < M := by rw [hM]; positivity
  have hL1 : M ≤ 1 + M := by linarith
  -- denominador: 8 (N+1)^s · L^κ ≥ 8 N^s · M^κ
  have hL_ge : M ^ κ ≤ Real.log (Real.exp 1 * N) ^ κ := by
    rw [hlogN]
    exact Real.rpow_le_rpow hMpos.le (by linarith) hκ
  have hNs_le : (N : ℝ) ^ s ≤ ((N : ℝ) + 1) ^ (max 1 s) := by
    calc (N : ℝ) ^ s ≤ ((N : ℝ) + 1) ^ s :=
          Real.rpow_le_rpow hNpos.le (by linarith) (by linarith)
      _ ≤ ((N : ℝ) + 1) ^ (max 1 s) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [hNpos]) (le_max_right _ _)
  have hH : 8 * (N : ℝ) ^ s * M ^ κ ≤ (Pendencias.Agenda.Hsk s κ N : ℝ) := by
    have h1 := Hsk_real_ge s κ N
    have hA : 0 ≤ (N : ℝ) ^ s := by positivity
    have hB : 0 ≤ Real.log (Real.exp 1 * N) ^ κ := by
      rw [hlogN]; positivity
    calc 8 * (N : ℝ) ^ s * M ^ κ ≤ 8 * ((N : ℝ) + 1) ^ (max 1 s) * Real.log (Real.exp 1 * N) ^ κ := by
          apply mul_le_mul (by linarith [hNs_le]) hL_ge (by positivity) (by positivity)
      _ ≤ _ := h1
  have hHpos : (0 : ℝ) < (Pendencias.Agenda.Hsk s κ N : ℝ) := by
    have : (0 : ℝ) < 8 * (N : ℝ) ^ s * M ^ κ := by positivity
    linarith
  rw [← ENNReal.ofReal_natCast (Pendencias.Agenda.Hsk s κ N), ← ENNReal.ofReal_div_of_pos hHpos]
  apply ENNReal.ofReal_le_ofReal
  have hx : (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) = (N : ℝ) ^ s := by
    rw [hNr, ← Real.rpow_mul (by norm_num)]
  have hNs : (0 : ℝ) < (N : ℝ) ^ s := by positivity
  have hMκ : 0 < M ^ κ := by positivity
  calc (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) / (Pendencias.Agenda.Hsk s κ N : ℝ)
      ≤ (N : ℝ) ^ s / (8 * (N : ℝ) ^ s * M ^ κ) := by
        rw [hx]
        exact div_le_div_of_nonneg_left hNs.le (by positivity) hH
    _ = 1 / 8 * (Real.log 2) ^ (-κ) * ((k + 1 : ℕ) : ℝ) ^ (-κ) := by
        have hMsplit : M ^ κ = (Real.log 2) ^ κ * ((k + 1 : ℕ) : ℝ) ^ κ := by
          rw [hM, Real.mul_rpow hkpos.le hlog2.le, mul_comm]
        rw [hMsplit, Real.rpow_neg hlog2.le, Real.rpow_neg hkpos.le]
        field_simp

/-- `H_{s,κ}(N) ≥ 8 N^{max 1 s}` para `N ≥ 1` e `κ ≥ 0` (o fator logarítmico é `≥ 1`). -/
theorem Hsk_low {s κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ) (hN : 1 ≤ N) :
    8 * (N : ℝ) ^ (max 1 s) ≤ (Pendencias.Agenda.Hsk s κ N : ℝ) := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL : 1 ≤ Real.log (Real.exp 1 * N) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have := Real.log_nonneg hNr
    linarith
  have hLk : 1 ≤ Real.log (Real.exp 1 * N) ^ κ := Real.one_le_rpow hL hκ
  have hν : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hNN : (N : ℝ) ^ (max 1 s) ≤ ((N : ℝ) + 1) ^ (max 1 s) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) hν
  have hA : 0 ≤ ((N : ℝ) + 1) ^ (max 1 s) := by positivity
  have h1 := Hsk_real_ge s κ N
  calc 8 * (N : ℝ) ^ (max 1 s) ≤ 8 * ((N : ℝ) + 1) ^ (max 1 s) := by linarith
    _ ≤ 8 * ((N : ℝ) + 1) ^ (max 1 s) * Real.log (Real.exp 1 * N) ^ κ := by
        apply le_mul_of_one_le_right (by positivity) hLk
    _ ≤ _ := h1

/-- `H̃_{s,η}(N) ≥ 8 N^{max 1 s}` para `N ≥ 1` e `η ≥ 0`. -/
theorem Htil_low {s η : ℝ} (hη : 0 ≤ η) (N : ℕ) (hN : 1 ≤ N) :
    8 * (N : ℝ) ^ (max 1 s) ≤ (Pendencias.Jackson.HtilK 0 0 s η N : ℝ) := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : max 1 s ≤ max 1 (s + η) := max_le_max le_rfl (by linarith)
  have h1 : (N : ℝ) ^ (max 1 s) ≤ (N : ℝ) ^ (max 1 (s + η)) :=
    Real.rpow_le_rpow_of_exponent_le hNr hexp
  have h2 : (N : ℝ) ^ (max 1 (s + η)) ≤ ((N : ℝ) + 1) ^ (max 1 (s + η)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (le_trans zero_le_one (le_max_left _ _))
  have h3 := Htil_real_ge s η N
  linarith

/-- Peso limitado: se `H(N) ≥ 8 N^{max 1 s}`, então `2^{(k+1)s}/H(2^{k+1}) ≤ 1/8`. -/
theorem weight_bdd (H : ℕ → ℕ) {s : ℝ} (hH : ∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ (max 1 s) ≤ (H N : ℝ))
    (k : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) / (H (2 ^ (k + 1)) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 8) := by
  set N : ℕ := 2 ^ (k + 1) with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNr : (N : ℝ) = (2 : ℝ) ^ (((k + 1 : ℕ)) : ℝ) := by
    rw [hNdef, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hHk := hH N hN1
  have hNν : 0 < (N : ℝ) ^ (max 1 s) := Real.rpow_pos_of_pos hNpos _
  have hHpos : (0 : ℝ) < (H N : ℝ) := by nlinarith
  have hx : (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) = (N : ℝ) ^ s := by
    rw [hNr, ← Real.rpow_mul (by norm_num)]
  have hsν : (N : ℝ) ^ s ≤ (N : ℝ) ^ (max 1 s) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (le_max_right _ _)
  rw [← ENNReal.ofReal_natCast (H N), ← ENNReal.ofReal_div_of_pos hHpos]
  apply ENNReal.ofReal_le_ofReal
  rw [hx]
  calc (N : ℝ) ^ s / (H N : ℝ) ≤ (N : ℝ) ^ (max 1 s) / (8 * (N : ℝ) ^ (max 1 s)) :=
        div_le_div₀ hNν.le hsν (by positivity) hHk
    _ = 1 / 8 := by field_simp

end FormalizacaoSched
