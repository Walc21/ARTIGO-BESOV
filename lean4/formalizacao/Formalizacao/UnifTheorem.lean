import Formalizacao.UnifCore
import Formalizacao.LowShift

/-!
# Seção 6, parte 4: dados de regime e Lema 6.2

Dados de regime `(ν', κ')`, `(ν̂, κ̂)` e `Λ_n` (`Definição lp:def:regime`), a agenda uniforme
`Ĥ^{[B]}_A(N) = ⌈A (B+1) (N+1)^{ν̂} [log(eN)]^{κ̂}⌉` e as propriedades (a) do `Lema
lp:lem:uniform-height`:
`Λ_n Q(n) ≤ 4 n^{ν̂} L(n)^{κ̂}`, onde `Q(n) = 2^{qexp}`.
-/

open scoped ENNReal
open FormalizacaoLp

namespace FormalizacaoLow

/-- `L(N) = log(e N)`. -/
noncomputable def Lfun (N : ℕ) : ℝ := Real.log (Real.exp 1 * N)

lemma one_le_Lfun {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Lfun N :=
  Pendencias.Agenda.log_eN_ge_one hN

lemma Lfun_mono : MonotoneOn Lfun (Set.Ici 1) := by
  intro m hm n _ hmn
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by exact hm)
  exact Real.log_le_log (mul_pos (Real.exp_pos _) hm')
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) (Real.exp_nonneg _))

lemma Lfun_two_pow (r : ℕ) : Lfun (2 ^ r) = 1 + (r : ℝ) * Real.log 2 := by
  unfold Lfun
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow]

/-- Expoente `ν'` da quantização. -/
noncomputable def nuPrime (p s : ℝ) : ℝ := if 1 / p < s then max 1 s else 1
/-- Expoente logarítmico `κ'` da quantização. -/
noncomputable def kapPrime (p s κ : ℝ) : ℝ := if s < 1 / p then 0 else κ
/-- Expoente `ν̂` da agenda uniforme. -/
noncomputable def nuHat (p s : ℝ) : ℝ :=
  if 1 / p < s then max 1 s else if s < 1 / p then 1 + 1 / p - s else 1
/-- Expoente logarítmico `κ̂` da agenda uniforme. -/
noncomputable def kapHat (p s : ℝ) (q : ℝ≥0∞) (κ : ℝ) : ℝ :=
  if 1 / p < s then κ else if s < 1 / p then 0 else thetaQ q + κ

/-- Agenda uniforme `Ĥ^{[B]}_A`. -/
noncomputable def Hunif (A B ν κ : ℝ) (N : ℕ) : ℕ :=
  ⌈A * (B + 1) * ((N : ℝ) + 1) ^ ν * Lfun N ^ κ⌉₊

/-- Fator logarítmico `L(2^r)^{κ'}` como função de `N`. -/
noncomputable def hfun (κ' : ℝ) (N : ℕ) : ℝ := Lfun N ^ κ'

lemma one_le_hfun {κ' : ℝ} (hκ : 0 ≤ κ') (r : ℕ) : 1 ≤ hfun κ' (2 ^ r) :=
  Real.one_le_rpow (one_le_Lfun Nat.one_le_two_pow) hκ

lemma one_le_nuPrime (p s : ℝ) : 1 ≤ nuPrime p s := by
  unfold nuPrime
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma kapPrime_nonneg (p s : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ kapPrime p s κ := by
  unfold kapPrime
  split_ifs
  · exact le_rfl
  · exact hκ

lemma s_le_nuPrime {p : ℝ} (hp : 1 ≤ p) (s : ℝ) : s ≤ nuPrime p s := by
  unfold nuPrime
  split_ifs with h
  · exact le_max_right _ _
  · have : 1 / p ≤ 1 := by rw [div_le_one (by linarith)]; exact hp
    linarith [not_lt.1 h]

lemma thetaQ_le_one (q : ℝ≥0∞) : thetaQ q ≤ 1 := by
  unfold thetaQ
  split_ifs with h
  · exact zero_le_one
  · have : 0 ≤ 1 / q.toReal := by positivity
    linarith

lemma nuHat_nonneg (p s : ℝ) (hp : 1 ≤ p) : 0 ≤ nuHat p s := by
  unfold nuHat
  split_ifs with h1 h2
  · exact le_trans zero_le_one (le_max_left _ _)
  · have : 0 < 1 / p := by positivity
    linarith
  · exact zero_le_one

lemma kapHat_nonneg (p s : ℝ) (q : ℝ≥0∞) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ kapHat p s q κ := by
  unfold kapHat
  split_ifs
  · exact hκ
  · exact le_rfl
  · exact add_nonneg (thetaQ_nonneg q) hκ

/-- Identidade `L(2^r)^κ` como `hfun κ (2^r)`. -/
lemma hfun_eq (k : ℝ) (r : ℕ) : hfun k (2 ^ r) = Lfun (2 ^ r) ^ k := rfl

/-- **Lema 6.2 (a)**, terceira desigualdade: `Λ_n Q(n) ≤ 4 n^{ν̂} L(n)^{κ̂}`. -/
lemma lamU_qexp_le {p : ℝ} (_hp : 1 ≤ p) (s : ℝ) (q : ℝ≥0∞) {κ : ℝ} (hκ : 0 ≤ κ) {r : ℕ}
    (hr : 1 ≤ r) :
    LamU p s q r * (2 : ℝ) ^ (qexp (nuPrime p s) (hfun (kapPrime p s κ)) r) ≤
      4 * (((2 : ℝ) ^ r) ^ (nuHat p s) * (Lfun (2 ^ r)) ^ (kapHat p s q κ)) := by
  have key0 := (qexp_spec (one_le_nuPrime p s) (h := hfun (kapPrime p s κ))
    (fun r => one_le_hfun (kapPrime_nonneg p s hκ) r) r).2.2
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hn : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hL1 : 1 ≤ Lfun (2 ^ r) := one_le_Lfun Nat.one_le_two_pow
  have hL0 : 0 < Lfun (2 ^ r) := by linarith
  by_cases hhigh : 1 / p < s
  · have hLam : LamU p s q r = 1 := by unfold LamU; rw [if_pos hhigh]
    have hν : nuPrime p s = nuHat p s := by
      unfold nuPrime nuHat; rw [if_pos hhigh, if_pos hhigh]
    have hk : kapPrime p s κ = kapHat p s q κ := by
      unfold kapPrime kapHat
      rw [if_neg (not_lt.2 (le_of_lt hhigh)), if_pos hhigh]
    have key := key0
    rw [hν, hk, hfun_eq] at key
    have hT : 0 ≤ ((2 : ℝ) ^ r) ^ (nuHat p s) * Lfun (2 ^ r) ^ (kapHat p s q κ) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hL0.le _)
    rw [hLam, one_mul, hν, hk]
    linarith
  · by_cases hlow : s < 1 / p
    · have hLam : LamU p s q r = (2 : ℝ) ^ ((r : ℝ) * (1 / p - s)) := by
        unfold LamU Lam; rw [if_neg hhigh, if_pos hlow]
      have hν : nuPrime p s = 1 := by unfold nuPrime; rw [if_neg hhigh]
      have hk : kapPrime p s κ = 0 := by unfold kapPrime; rw [if_pos hlow]
      have hν2 : nuHat p s = 1 + 1 / p - s := by
        unfold nuHat; rw [if_neg hhigh, if_pos hlow]
      have hk2 : kapHat p s q κ = 0 := by
        unfold kapHat; rw [if_neg hhigh, if_pos hlow]
      have key := key0
      rw [hν, hk, hfun_eq] at key
      rw [Real.rpow_zero, Real.rpow_one, mul_one] at key
      have hδ : 0 ≤ 1 / p - s := by linarith
      have hX : 0 ≤ (2 : ℝ) ^ ((r : ℝ) * (1 / p - s)) := by positivity
      have hid : ((2 : ℝ) ^ r) ^ (1 + 1 / p - s) =
          (2 : ℝ) ^ r * (2 : ℝ) ^ ((r : ℝ) * (1 / p - s)) := by
        rw [← Real.rpow_natCast (2 : ℝ) r, ← Real.rpow_mul (by norm_num),
          show (r : ℝ) * (1 + 1 / p - s) = (r : ℝ) + (r : ℝ) * (1 / p - s) by ring,
          Real.rpow_add (by norm_num)]
      rw [hLam, hν, hk, hν2, hk2, Real.rpow_zero, mul_one, hid]
      refine le_trans (mul_le_mul_of_nonneg_left key hX) ?_
      nlinarith [hX, hn]
    · have hLam : LamU p s q r = (r : ℝ) ^ thetaQ q := by
        unfold LamU Lam; rw [if_neg hhigh, if_neg hlow]
      have hν : nuPrime p s = 1 := by unfold nuPrime; rw [if_neg hhigh]
      have hk : kapPrime p s κ = κ := by unfold kapPrime; rw [if_neg hlow]
      have hν2 : nuHat p s = 1 := by unfold nuHat; rw [if_neg hhigh, if_neg hlow]
      have hk2 : kapHat p s q κ = thetaQ q + κ := by
        unfold kapHat; rw [if_neg hhigh, if_neg hlow]
      have key := key0
      rw [hν, hk, hfun_eq, Real.rpow_one] at key
      have hθ : 0 ≤ thetaQ q := thetaQ_nonneg q
      have hθ1 : thetaQ q ≤ 1 := thetaQ_le_one q
      have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have hrL : (r : ℝ) ≤ 2 * Lfun (2 ^ r) := by
        rw [Lfun_two_pow]; nlinarith
      have hrθ : (r : ℝ) ^ thetaQ q ≤ 2 * Lfun (2 ^ r) ^ thetaQ q := by
        have hpow : (2 : ℝ) ^ thetaQ q ≤ 2 := by
          calc (2 : ℝ) ^ thetaQ q ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
            _ = 2 := Real.rpow_one 2
        calc (r : ℝ) ^ thetaQ q ≤ (2 * Lfun (2 ^ r)) ^ thetaQ q :=
              Real.rpow_le_rpow hr0.le hrL hθ
          _ = 2 ^ thetaQ q * Lfun (2 ^ r) ^ thetaQ q := Real.mul_rpow (by norm_num) hL0.le
          _ ≤ 2 * Lfun (2 ^ r) ^ thetaQ q :=
              mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hL0.le _)
      have hc : 0 ≤ 2 * ((2 : ℝ) ^ r * Lfun (2 ^ r) ^ κ) :=
        mul_nonneg (by norm_num) (mul_nonneg hn.le (Real.rpow_nonneg hL0.le _))
      rw [hLam, hν, hk, hν2, hk2, Real.rpow_one, Real.rpow_add hL0]
      refine le_trans (mul_le_mul_of_nonneg_left key (by positivity)) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hrθ hc) (le_of_eq (by ring))


open MeasureTheory FormalizacaoRed FormalizacaoLq

/-- Admissibilidade para somar o erro de quantização nas escalas diádicas. -/
def UniformAdmissible (s : ℝ) (q : ℝ≥0∞) (κ : ℝ) : Prop :=
  q ≠ ⊤ → 1 ≤ s → 1 / q.toReal < κ

/-- A potência `2^qexp` é a menor potência de dois que atinge o alvo. -/
lemma qexp_le_of_target_le {ν : ℝ} {h : ℕ → ℝ} {r j : ℕ} (hh : 0 < h (2 ^ r))
    (hj : ((2 : ℝ) ^ r) ^ ν * h (2 ^ r) ≤ (2 : ℝ) ^ j) : qexp ν h r ≤ j := by
  have he : (2 : ℝ) ^ (ν * (r : ℝ) + Real.logb 2 (h (2 ^ r))) =
      ((2 : ℝ) ^ r) ^ ν * h (2 ^ r) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hh,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (r : ℝ) ν]
  apply Nat.ceil_le.mpr
  apply (Real.rpow_le_rpow_left_iff (by norm_num : 1 < (2 : ℝ))).mp
  rwa [he, Real.rpow_natCast]

lemma qexp_s_le {s ν : ℝ} (hν : 1 ≤ ν) (hsν : s ≤ ν) {h : ℕ → ℝ}
    (hh : ∀ r, 1 ≤ h (2 ^ r)) (r : ℕ) : (2 : ℝ) ^ ((r : ℝ) * s) ≤ 2 ^ (qexp ν h r) := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  calc ((2 : ℝ) ^ r) ^ s ≤ ((2 : ℝ) ^ r) ^ ν :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hsν
    _ ≤ ((2 : ℝ) ^ r) ^ ν * h (2 ^ r) := le_mul_of_one_le_right (by positivity) (hh r)
    _ ≤ _ := (qexp_spec hν hh r).2.1

/-- Lema 6.2(a), incluindo o controle de `1/Q` pela escala `n^{-s}`. -/
theorem uniform_height_quantization {p : ℝ} (hp : 1 ≤ p) (s : ℝ) (q : ℝ≥0∞)
    {κ : ℝ} (hκ : 0 ≤ κ) {r : ℕ} (hr : 1 ≤ r) :
    let Q : ℝ := 2 ^ qexp (nuPrime p s) (hfun (kapPrime p s κ)) r
    (2 : ℝ) ^ r ≤ Q ∧
      Q ≤ 2 * (((2 : ℝ) ^ r) ^ nuPrime p s * Lfun (2 ^ r) ^ kapPrime p s κ) ∧
      1 / Q ≤ ((2 : ℝ) ^ r) ^ (-s) ∧
      LamU p s q r * Q ≤ 4 * (((2 : ℝ) ^ r) ^ nuHat p s * Lfun (2 ^ r) ^ kapHat p s q κ) := by
  have hh := one_le_hfun (kapPrime_nonneg p s hκ)
  have hQ := qexp_spec (one_le_nuPrime p s) hh r
  refine ⟨pow_le_pow_right₀ (by norm_num) hQ.1, hQ.2.2, ?_, lamU_qexp_le hp s q hκ hr⟩
  rw [Real.rpow_neg (by positivity), ← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  rw [← Real.rpow_natCast (2 : ℝ) r, ← Real.rpow_mul (by norm_num)]
  exact qexp_s_le (one_le_nuPrime p s) (s_le_nuPrime hp s) hh r

/-- Lema 6.2(c), com o fator `1/2` da estimativa nodal. -/
theorem uniform_quantWeight_lt_top {p : ℝ} (hp : 1 ≤ p) {s : ℝ} {q : ℝ≥0∞}
    (hq : 0 < q) {κ : ℝ} (hκ : 0 ≤ κ) (ha : UniformAdmissible s q κ) :
    lqNorm q (quantWeight s (qexp (nuPrime p s) (hfun (kapPrime p s κ)))) < ⊤ := by
  set e := qexp (nuPrime p s) (hfun (kapPrime p s κ))
  have hh := one_le_hfun (kapPrime_nonneg p s hκ)
  have hQ := qexp_spec (one_le_nuPrime p s) hh
  have hw (k : ℕ) : quantWeight s e k =
      ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) / (2 * 2 ^ (e (k + 1)))) := by
    unfold quantWeight
    rw [← ENNReal.ofReal_mul (by positivity), ← div_eq_mul_one_div]
  by_cases hqt : q = ⊤
  · rw [hqt, lqNorm, if_pos rfl]
    refine lt_of_le_of_lt (b := 1) (iSup_le fun k ↦ ?_) (by norm_num)
    rw [hw, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (by positivity), one_mul]
    have := qexp_s_le (one_le_nuPrime p s) (s_le_nuPrime hp s) hh (k + 1)
    dsimp [e] at *
    linarith [show (0 : ℝ) ≤ 2 ^ (qexp (nuPrime p s) (hfun (kapPrime p s κ)) (k + 1)) by positivity]
  by_cases hs : s < 1
  · let ρ := (2 : ℝ) ^ (s - 1)
    refine lq_geom_all hq (C := ρ / 2) (ρ := ρ) (by dsimp [ρ]; positivity)
      (by dsimp [ρ]; positivity) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hs))
      fun k ↦ ?_
    rw [hw]
    apply ENNReal.ofReal_le_ofReal
    calc _ ≤ (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s) / (2 * 2 ^ (k + 1)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num) (hQ (k + 1)).1) (by norm_num))
      _ ≤ _ := by simpa only [ρ, Nat.add_zero, ← div_eq_mul_one_div] using wreal_geom s k 0
  have hs1 : 1 ≤ s := le_of_not_gt hs
  have hp1 : 1 / p ≤ 1 := (div_le_one (by linarith)).mpr hp
  have hν : nuPrime p s = s := by
    unfold nuPrime
    split_ifs with h
    · exact max_eq_right hs1
    · linarith
  have hk : kapPrime p s κ = κ := if_neg (not_lt.mpr (hp1.trans hs1))
  have hqR := ENNReal.toReal_pos hq.ne' hqt
  have hκq : 1 < κ * q.toReal := (div_lt_iff₀ hqR).mp (ha hqt hs1)
  refine lq_of_poly_le hq hqt (D := (1 / 2) * (Real.log 2) ^ (-κ))
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _))
    hκq fun k ↦ ?_
  rw [hw]
  apply ENNReal.ofReal_le_ofReal
  let r := k + 1
  have hr : 0 < (r : ℝ) := by dsimp [r]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : ((r : ℝ) * Real.log 2) ^ κ ≤ Lfun (2 ^ r) ^ κ := by
    rw [Lfun_two_pow]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hκ
  have htarget : (2 : ℝ) ^ ((r : ℝ) * s) * ((r : ℝ) * Real.log 2) ^ κ ≤ 2 ^ e r := by
    have h := (hQ r).2.1
    rw [hν, hk, hfun_eq, ← Real.rpow_natCast (2 : ℝ) r, ← Real.rpow_mul (by norm_num)] at h
    rw [show e r = qexp s (hfun κ) r by simp only [e, hν, hk]]
    exact (mul_le_mul_of_nonneg_left hL (by positivity)).trans h
  calc _ ≤ (2 : ℝ) ^ ((r : ℝ) * s) / (2 * ((2 : ℝ) ^ ((r : ℝ) * s) *
            ((r : ℝ) * Real.log 2) ^ κ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left htarget (by norm_num))
    _ = _ := by
        rw [Real.mul_rpow hr.le hlog.le, Real.rpow_neg hlog.le, Real.rpow_neg hr.le]
        field_simp

/-- Altura suficiente para a aplicação do núcleo uniforme na agenda da Definição 6.1. -/
lemma uniform_budget {p : ℝ} (hp : 1 ≤ p) (s : ℝ) (q : ℝ≥0∞) {κ B Cs : ℝ}
    (hκ : 0 ≤ κ) (hB : 1 ≤ B) (hCs : 1 ≤ Cs) {r : ℕ} (hr : 1 ≤ r) :
    8 * (Cs * B * LamU p s q r + 1) * 2 ^ (qexp (nuPrime p s) (hfun (kapPrime p s κ)) r) ≤
      (Hunif (32 * (Cs + 1)) B (nuHat p s) (kapHat p s q κ) (2 ^ r) : ℝ) := by
  let Q : ℝ := 2 ^ (qexp (nuPrime p s) (hfun (kapPrime p s κ)) r)
  have hΛ := one_le_LamU p s q hr
  have hc : Cs * B * LamU p s q r + 1 ≤ (Cs + 1) * (B + 1) * LamU p s q r := by
    calc _ ≤ (Cs * B + 1) * LamU p s q r := by linarith
      _ ≤ _ := by gcongr; nlinarith
  calc _ ≤ 8 * ((Cs + 1) * (B + 1) * LamU p s q r) * Q := by gcongr
    _ = (8 * (Cs + 1) * (B + 1)) * (LamU p s q r * Q) := by ring
    _ ≤ (8 * (Cs + 1) * (B + 1)) *
        (4 * (((2 : ℝ) ^ r) ^ nuHat p s * Lfun (2 ^ r) ^ kapHat p s q κ)) :=
          mul_le_mul_of_nonneg_left (lamU_qexp_le hp s q hκ hr) (by positivity)
    _ ≤ _ := by
      apply le_trans _ (Nat.le_ceil _)
      push_cast
      calc _ = (32 * (Cs + 1)) * (B + 1) *
          ((2 : ℝ) ^ r) ^ nuHat p s * Lfun (2 ^ r) ^ kapHat p s q κ := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg
            ((one_le_Lfun (N := 2 ^ r) Nat.one_le_two_pow).trans' zero_le_one) _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow (by positivity) (le_add_of_nonneg_right zero_le_one)
            (nuHat_nonneg p s hp)


/-- Conclusões pontual e em `ℓ^q` de um controle uniforme de altura e quantização. -/
theorem uniform_ball_of_budget {p : ℝ} (hp : 1 ≤ p) {s : ℝ} {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ CW Cs : ℝ, 0 ≤ CW ∧ 1 ≤ Cs ∧ ∀ (e : ℕ → ℕ) (height : ℝ → ℝ → ℕ → ℕ),
      (∀ r, 1 ≤ r → r ≤ e r) →
      (∀ r : ℕ, 1 ≤ r → (2 : ℝ) ^ ((r : ℝ) * s) ≤ 2 ^ e r) →
      (∀ B : ℝ, 1 ≤ B → ∀ r, 1 ≤ r →
        8 * (Cs * B * LamU p s q r + 1) * 2 ^ (e r) ≤ (height Cs B (2 ^ r) : ℝ)) →
      (∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
        besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
        ∀ r, 1 ≤ r → ∃ g ∈ classNH (2 ^ r) (height Cs B (2 ^ r)),
          distP (ENNReal.ofReal p) f g ≤
            9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
              ENNReal.ofReal (1 / (2 * 2 ^ (e r))) ∧
          9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
              ENNReal.ofReal (1 / (2 * 2 ^ (e r))) ≤
            ENNReal.ofReal ((9 * CW * B + 1) * ((2 : ℝ) ^ r) ^ (-s)) ∧
          realP (ENNReal.ofReal p) (Pendencias.Agenda.Sigma (height Cs B)) (2 ^ r) f ≤
            ENNReal.ofReal (((1 + 45 * CW) * B + 5 / 2) * ((2 : ℝ) ^ r) ^ (-s))) ∧
      (lqNorm q (quantWeight s e) < ⊤ → ∃ C : ℝ, 0 ≤ C ∧
        ∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
          besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
          lqNorm q (stratSeq (ENNReal.ofReal p) s (Pendencias.Agenda.Sigma (height Cs B)) f) ≤
            ENNReal.ofReal (C * (B + 1))) := by
  obtain ⟨CW, Cs, hCW, hCs, hcore⟩ := unif_core (p := p) (s := s) hp hq
  refine ⟨CW, Cs, hCW, hCs, fun e height he hQ hH ↦ ⟨?_, ?_⟩⟩
  · intro B hB f hf hb r hr
    obtain ⟨g, hg, hD, hR⟩ := hcore B hB e (height Cs B) he (hH B hB) f hf hb r hr
    refine ⟨g, hg, hD, ?_⟩
    let P := ENNReal.ofReal p
    let x : ℝ := (2 : ℝ) ^ ((r : ℝ) * s)
    have hx : 0 < x := by dsimp [x]; positivity
    have hb' : ENNReal.ofReal x * wtP P (1 / (2 : ℝ) ^ r) f ≤ ENNReal.ofReal B :=
      (le_iSup (besovSeq P s f) r).trans ((iSup_le_lq hq _).trans
        ((lqNorm_le_besovNorm P s q f).trans hb))
    have hw : wtP P (1 / (2 : ℝ) ^ r) f ≤ ENNReal.ofReal (B / x) := by
      rw [ENNReal.ofReal_div_of_pos hx]
      exact ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hx)) (Or.inl ENNReal.ofReal_ne_top) |>.mpr
        (by simpa only [mul_comm] using hb')
    have he' : 1 / (2 * (2 : ℝ) ^ e r) ≤ 1 / x := by
      apply one_div_le_one_div_of_le hx
      linarith [hQ r hr, show (0 : ℝ) ≤ 2 ^ e r by positivity]
    have hx' : x⁻¹ = ((2 : ℝ) ^ r) ^ (-s) := by
      dsimp [x]
      rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast (2 : ℝ) r,
        ← Real.rpow_mul (by norm_num)]
    constructor
    · calc _ ≤ 9 * ENNReal.ofReal CW * ENNReal.ofReal (B / x) + ENNReal.ofReal (1 / x) :=
            add_le_add (mul_le_mul_right hw _) (ENNReal.ofReal_le_ofReal he')
        _ = _ := by
          rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
            div_eq_mul_inv, one_div, hx']
          congr 1
          ring
    · have heHalf : 1 / (2 * (2 : ℝ) ^ e r) ≤ (1 / 2) / x := by
        rw [div_le_div_iff₀ (by positivity) hx]
        have hxQ : x ≤ (2 : ℝ) ^ e r := hQ r hr
        linarith
      refine hR.trans ?_
      calc _ ≤ ENNReal.ofReal (B / x) +
            5 * (9 * ENNReal.ofReal CW * ENNReal.ofReal (B / x) +
              ENNReal.ofReal ((1 / 2) / x)) := by
            gcongr
        _ = _ := by
          simp only [← ENNReal.ofReal_ofNat]
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          rw [← hx']
          congr 1
          ring
  · intro hw
    let W := lqNorm q (quantWeight s e)
    let K : ℝ≥0∞ := 2 * (2 : ℝ≥0∞) ^ q.toReal⁻¹
    let a : ℝ≥0∞ := 1 + 5 * (9 * ENNReal.ofReal CW)
    let D := K * (a + 5 * W)
    have hD : D ≠ ⊤ := by
      dsimp [D, K, a, W]
      finiteness
    refine ⟨D.toReal, ENNReal.toReal_nonneg, fun B hB f hf hb ↦ ?_⟩
    have hR := unif_rate_of_scale hq hb fun r hr ↦
      (hcore B hB e (height Cs B) he (hH B hB) f hf hb r hr).choose_spec.2.2
    have hB1 : 1 ≤ ENNReal.ofReal (B + 1) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc _ ≤ K * (a * ENNReal.ofReal B + 5 * W) := hR
      _ ≤ K * (a * ENNReal.ofReal (B + 1) + (5 * W) * ENNReal.ofReal (B + 1)) := by
        exact mul_le_mul_right (add_le_add
          (mul_le_mul_right (ENNReal.ofReal_le_ofReal (by linarith)) a)
          (le_mul_of_one_le_right' hB1)) K
      _ = ENNReal.ofReal (D.toReal * (B + 1)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hD]
        simp only [D, add_mul, mul_assoc]

/-- Teorema 6.3 com uma única agenda, para todos os raios e escalas diádicas. -/
theorem uniform_besov_ball {p : ℝ} (hp : 1 ≤ p) {s : ℝ} {q : ℝ≥0∞} (hq : 0 < q) (_hs2 : s < 2) :
    ∃ CW Cs : ℝ, 0 ≤ CW ∧ 1 ≤ Cs ∧ ∀ κ : ℝ, 0 ≤ κ →
      (∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
        besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
        ∀ r, 1 ≤ r →
          let H := Hunif (32 * (Cs + 1)) B (nuHat p s) (kapHat p s q κ)
          let Q : ℝ := 2 ^ qexp (nuPrime p s) (hfun (kapPrime p s κ)) r
          let E := 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
            ENNReal.ofReal (1 / (2 * Q))
          ∃ g ∈ classNH (2 ^ r) (H (2 ^ r)), distP (ENNReal.ofReal p) f g ≤ E ∧
            E ≤ ENNReal.ofReal ((9 * CW * B + 1) * ((2 : ℝ) ^ r) ^ (-s)) ∧
            realP (ENNReal.ofReal p) (Pendencias.Agenda.Sigma H) (2 ^ r) f ≤
              ENNReal.ofReal (((1 + 45 * CW) * B + 5 / 2) * ((2 : ℝ) ^ r) ^ (-s))) ∧
      (UniformAdmissible s q κ → ∃ C : ℝ, 0 ≤ C ∧
        ∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
          besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
          lqNorm q (stratSeq (ENNReal.ofReal p) s
            (Pendencias.Agenda.Sigma (Hunif (32 * (Cs + 1)) B (nuHat p s) (kapHat p s q κ))) f) ≤
            ENNReal.ofReal (C * (B + 1))) := by
  obtain ⟨CW, Cs, hCW, hCs, hunif⟩ := uniform_ball_of_budget (s := s) hp hq
  refine ⟨CW, Cs, hCW, hCs, fun κ hκ ↦ ?_⟩
  have hh := one_le_hfun (kapPrime_nonneg p s hκ)
  obtain ⟨happ, hrate⟩ := hunif
    (qexp (nuPrime p s) (hfun (kapPrime p s κ)))
    (fun Cs B ↦ Hunif (32 * (Cs + 1)) B (nuHat p s) (kapHat p s q κ))
    (fun r _ ↦ (qexp_spec (one_le_nuPrime p s) hh r).1)
    (fun r _ ↦ qexp_s_le (one_le_nuPrime p s) (s_le_nuPrime hp s) hh r)
    (fun _ hB _ hr ↦ uniform_budget hp s q hκ hB hCs hr)
  exact ⟨happ, fun ha ↦ hrate (uniform_quantWeight_lt_top hp hq hκ ha)⟩

end FormalizacaoLow
