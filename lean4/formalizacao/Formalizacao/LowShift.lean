import Formalizacao.LowSup
import Formalizacao.LowWeights

/-!
# Regimes `s ≤ 1/p`, parte 8: a condição de deslocamento

Para cada uma das agendas
* `s < 1/p`: `H(N) = Hsk (1 + 1/p - s) 0 N = ⌈8 (N+1)^{1+1/p-s}⌉`,
* `s = 1/p`: `H(N) = Hsk 1 (θ_q + κ) N = ⌈8 (N+1) [log(eN)]^{θ_q+κ}⌉`,

mostra-se que, para todo `K ≥ 1`, existe `e0` com `8 (K Λ_r + 1) 2^{r + m r} ≤ H(2^{r+e0})`
(`r ≥ 1`), onde `m = 0` (caso `s < 1/p`) e `m = mDiag κ` (caso `s = 1/p`).
-/

open scoped ENNReal

namespace FormalizacaoLow

open FormalizacaoSched

theorem hshift_low {p s : ℝ} (hs : s < 1 / p) (q : ℝ≥0∞) (m : ℕ → ℕ) (hm : ∀ r, m r = 0) :
    ∀ K : ℝ, 1 ≤ K → ∃ e0 : ℕ, ∀ r : ℕ, 1 ≤ r →
      8 * (K * Lam p s q r + 1) * 2 ^ (r + m r) ≤
        (Pendencias.Agenda.Hsk (1 + 1 / p - s) 0 (2 ^ (r + e0)) : ℝ) := by
  intro K hK
  set δ : ℝ := 1 / p - s with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨⌈K + 1⌉₊, fun r hr => ?_⟩
  set e0 : ℕ := ⌈K + 1⌉₊ with he0def
  have hLam : Lam p s q r = (2 : ℝ) ^ ((r : ℝ) * δ) := by
    unfold Lam; rw [if_pos hs]
  rw [hLam, hm r, add_zero]
  set a : ℝ := 1 + 1 / p - s with ha
  have ha_eq : a = 1 + δ := by rw [ha, hδ]; ring
  have ha1 : 1 ≤ a := by rw [ha_eq]; linarith
  have hHsk := Hsk_real_ge a 0 (2 ^ (r + e0))
  rw [Real.rpow_zero, mul_one, max_eq_right ha1] at hHsk
  have hX1 : 1 ≤ (2 : ℝ) ^ ((r : ℝ) * δ) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg r) hδ0.le)
  have hprod : (2 : ℝ) ^ ((r : ℝ) * δ) * 2 ^ r = (2 : ℝ) ^ ((r : ℝ) * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    rw [ha_eq]; ring
  have hNa : (2 : ℝ) ^ ((r : ℝ) * a) * (2 : ℝ) ^ ((e0 : ℝ) * a) ≤
      (((2 ^ (r + e0) : ℕ) : ℝ) + 1) ^ a := by
    have h1 : ((2 ^ (r + e0) : ℕ) : ℝ) ^ a ≤ (((2 ^ (r + e0) : ℕ) : ℝ) + 1) ^ a :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
    have h2 : ((2 ^ (r + e0) : ℕ) : ℝ) ^ a =
        (2 : ℝ) ^ ((r : ℝ) * a) * (2 : ℝ) ^ ((e0 : ℝ) * a) := by
      rw [← Real.rpow_add (by norm_num), Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    linarith
  have he : K + 1 ≤ (2 : ℝ) ^ ((e0 : ℝ) * a) := by
    have h1 : K + 1 ≤ (e0 : ℝ) := Nat.le_ceil _
    have h2 : (e0 : ℝ) < 2 ^ e0 := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : (2 : ℝ) ^ e0 ≤ (2 : ℝ) ^ ((e0 : ℝ) * a) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith [Nat.cast_nonneg (α := ℝ) e0])
    linarith
  have hP : 0 < (2 : ℝ) ^ ((r : ℝ) * a) := Real.rpow_pos_of_pos (by norm_num) _
  calc 8 * (K * (2 : ℝ) ^ ((r : ℝ) * δ) + 1) * 2 ^ r
      ≤ 8 * ((K + 1) * (2 : ℝ) ^ ((r : ℝ) * δ)) * 2 ^ r := by
        gcongr; linarith
    _ = 8 * (2 : ℝ) ^ ((r : ℝ) * a) * (K + 1) := by rw [← hprod]; ring
    _ ≤ 8 * (2 : ℝ) ^ ((r : ℝ) * a) * (2 : ℝ) ^ ((e0 : ℝ) * a) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = 8 * ((2 : ℝ) ^ ((r : ℝ) * a) * (2 : ℝ) ^ ((e0 : ℝ) * a)) := by ring
    _ ≤ 8 * (((2 ^ (r + e0) : ℕ) : ℝ) + 1) ^ a := by linarith
    _ ≤ _ := hHsk

theorem hshift_diag {p : ℝ} {q : ℝ≥0∞} {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ K : ℝ, 1 ≤ K → ∃ e0 : ℕ, ∀ r : ℕ, 1 ≤ r →
      8 * (K * Lam p (1 / p) q r + 1) * 2 ^ (r + mDiag κ r) ≤
        (Pendencias.Agenda.Hsk 1 (thetaQ q + κ) (2 ^ (r + e0)) : ℝ) := by
  intro K hK
  set θ := thetaQ q with hθdef
  have hθ : 0 ≤ θ := thetaQ_nonneg q
  set ϑ : ℝ := θ + κ with hϑdef
  have hϑ : 0 ≤ ϑ := add_nonneg hθ hκ
  refine ⟨⌈ϑ + 1⌉₊ + ⌈K + 1⌉₊, fun r hr => ?_⟩
  set e0 : ℕ := ⌈ϑ + 1⌉₊ + ⌈K + 1⌉₊ with he0def
  have hr0 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hLam : Lam p (1 / p) q r = (r : ℝ) ^ θ := by
    unfold Lam; rw [if_neg (lt_irrefl _)]
  rw [hLam]
  have hrθ : 1 ≤ (r : ℝ) ^ θ := Real.one_le_rpow hr0 hθ
  have hm := mDiag_le hκ hr
  have hrϑ : (r : ℝ) ^ ϑ = (r : ℝ) ^ θ * (r : ℝ) ^ κ := Real.rpow_add hrpos _ _
  have hrκ : 0 < (r : ℝ) ^ κ := Real.rpow_pos_of_pos hrpos _
  have hleft : 8 * (K * (r : ℝ) ^ θ + 1) * 2 ^ (r + mDiag κ r) ≤
      16 * (K + 1) * 2 ^ r * (r : ℝ) ^ ϑ := by
    rw [pow_add, hrϑ]
    calc 8 * (K * (r : ℝ) ^ θ + 1) * (2 ^ r * 2 ^ mDiag κ r)
        ≤ 8 * ((K + 1) * (r : ℝ) ^ θ) * (2 ^ r * (2 * (r : ℝ) ^ κ)) := by
          gcongr
          nlinarith
      _ = 16 * (K + 1) * 2 ^ r * ((r : ℝ) ^ θ * (r : ℝ) ^ κ) := by ring
  -- cota inferior de `Hsk`
  have hH := Hsk_real_ge 1 ϑ (2 ^ (r + e0))
  rw [max_self, Real.rpow_one] at hH
  have hlog : Real.log (Real.exp 1 * ((2 ^ (r + e0) : ℕ) : ℝ)) =
      1 + ((r + e0 : ℕ) : ℝ) * Real.log 2 := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Nat.cast_pow,
      Nat.cast_ofNat, Real.log_pow]
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLg : (r : ℝ) / 2 ≤ Real.log (Real.exp 1 * ((2 ^ (r + e0) : ℕ) : ℝ)) := by
    rw [hlog]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) e0]
  have hLgϑ : ((r : ℝ) / 2) ^ ϑ ≤
      Real.log (Real.exp 1 * ((2 ^ (r + e0) : ℕ) : ℝ)) ^ ϑ :=
    Real.rpow_le_rpow (by positivity) hLg hϑ
  have hdiv : ((r : ℝ) / 2) ^ ϑ = (r : ℝ) ^ ϑ / (2 : ℝ) ^ ϑ :=
    Real.div_rpow hrpos.le (by norm_num) ϑ
  have h2ϑ : 0 < (2 : ℝ) ^ ϑ := Real.rpow_pos_of_pos (by norm_num) _
  have hrϑpos : 0 < (r : ℝ) ^ ϑ := Real.rpow_pos_of_pos hrpos _
  have hN : ((2 ^ (r + e0) : ℕ) : ℝ) = 2 ^ r * 2 ^ e0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_add]
  have he0 : 2 * (K + 1) * (2 : ℝ) ^ ϑ ≤ 2 ^ e0 := by
    have h1 : (2 : ℝ) ^ (ϑ + 1) ≤ (2 : ℝ) ^ (⌈ϑ + 1⌉₊) := by
      calc (2 : ℝ) ^ (ϑ + 1) ≤ (2 : ℝ) ^ ((⌈ϑ + 1⌉₊ : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
        _ = (2 : ℝ) ^ (⌈ϑ + 1⌉₊) := Real.rpow_natCast _ _
    have h2 : K + 1 ≤ (2 : ℝ) ^ (⌈K + 1⌉₊) := by
      have h3 : K + 1 ≤ (⌈K + 1⌉₊ : ℝ) := Nat.le_ceil _
      have h4 : (⌈K + 1⌉₊ : ℝ) < 2 ^ (⌈K + 1⌉₊) := by exact_mod_cast Nat.lt_two_pow_self
      linarith
    have h5 : (2 : ℝ) ^ (ϑ + 1) = 2 * (2 : ℝ) ^ ϑ := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
    rw [he0def, pow_add]
    calc 2 * (K + 1) * (2 : ℝ) ^ ϑ = (2 * (2 : ℝ) ^ ϑ) * (K + 1) := by ring
      _ ≤ (2 : ℝ) ^ (⌈ϑ + 1⌉₊) * (2 : ℝ) ^ (⌈K + 1⌉₊) := by
          rw [← h5]
          exact mul_le_mul h1 h2 (by linarith) (by positivity)
  have hq' : 2 * (K + 1) ≤ (2 : ℝ) ^ e0 / (2 : ℝ) ^ ϑ := by
    rw [le_div_iff₀ h2ϑ]; exact he0
  have hright : 16 * (K + 1) * 2 ^ r * (r : ℝ) ^ ϑ ≤
      8 * (((2 ^ (r + e0) : ℕ) : ℝ) + 1) *
        Real.log (Real.exp 1 * ((2 ^ (r + e0) : ℕ) : ℝ)) ^ ϑ := by
    have h1 : 8 * ((2 : ℝ) ^ r * (r : ℝ) ^ ϑ) * (2 * (K + 1)) ≤
        8 * ((2 : ℝ) ^ r * (r : ℝ) ^ ϑ) * ((2 : ℝ) ^ e0 / (2 : ℝ) ^ ϑ) :=
      mul_le_mul_of_nonneg_left hq' (by positivity)
    have h2 : 8 * ((2 : ℝ) ^ r * (r : ℝ) ^ ϑ) * ((2 : ℝ) ^ e0 / (2 : ℝ) ^ ϑ) =
        8 * ((2 : ℝ) ^ r * (2 : ℝ) ^ e0) * ((r : ℝ) ^ ϑ / (2 : ℝ) ^ ϑ) := by
      field_simp
    have h3 : 8 * ((2 : ℝ) ^ r * (2 : ℝ) ^ e0) * ((r : ℝ) ^ ϑ / (2 : ℝ) ^ ϑ) ≤
        8 * (((2 ^ (r + e0) : ℕ) : ℝ) + 1) *
          Real.log (Real.exp 1 * ((2 ^ (r + e0) : ℕ) : ℝ)) ^ ϑ := by
      rw [← hdiv, ← hN] at *
      have hNp : (0 : ℝ) ≤ ((2 ^ (r + e0) : ℕ) : ℝ) := Nat.cast_nonneg _
      calc 8 * ((2 ^ (r + e0) : ℕ) : ℝ) * ((r : ℝ) / 2) ^ ϑ
          ≤ 8 * (((2 ^ (r + e0) : ℕ) : ℝ) + 1) * ((r : ℝ) / 2) ^ ϑ := by
            gcongr; linarith
        _ ≤ 8 * (((2 ^ (r + e0) : ℕ) : ℝ) + 1) *
              Real.log (Real.exp 1 * ((2 ^ (r + e0) : ℕ) : ℝ)) ^ ϑ :=
            mul_le_mul_of_nonneg_left hLgϑ (by positivity)
    have h4 : 16 * (K + 1) * 2 ^ r * (r : ℝ) ^ ϑ =
        8 * ((2 : ℝ) ^ r * (r : ℝ) ^ ϑ) * (2 * (K + 1)) := by ring
    linarith
  exact (hleft.trans hright).trans hH

end FormalizacaoLow
