import Formalizacao.IteratedSchedules
import Formalizacao.LpJackson3
import Formalizacao.LowTheorems

/-!
# Agendas de logaritmo iterado (seção 6.3)

Uma segunda condensação de Cauchy reduz a série de log-log à série de potências
de expoente `-γq`. A igualdade dos espaços e ambas as estabilidades seguem
dos teoremas de transferência existentes.
-/

open scoped ENNReal
open Set MeasureTheory FormalizacaoLp FormalizacaoLow FormalizacaoRed FormalizacaoLq
open FormalizacaoRegular

namespace FormalizacaoLogLog

/-- Segundo logaritmo da agenda, `1 + log L₁(N)`. -/
noncomputable def Ltwo (N : ℕ) : ℝ := 1 + Real.log (Lfun N)

lemma one_le_Ltwo {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Ltwo N :=
  le_add_of_nonneg_right (Real.log_nonneg (one_le_Lfun hN))

lemma Ltwo_mono : MonotoneOn Ltwo (Ici 1) := by
  intro m hm n hn hmn
  unfold Ltwo
  exact add_le_add_right (Real.log_le_log (zero_lt_one.trans_le (one_le_Lfun hm))
    (Lfun_mono hm hn hmn)) _

/-- Fator `L₁(N)^{1/q} L₂(N)^γ`. -/
noncomputable def logLogFactor (q : ℝ≥0∞) (γ : ℝ) (N : ℕ) : ℝ :=
  Lfun N ^ q.toReal⁻¹ * Ltwo N ^ γ

lemma one_le_logLogFactor (q : ℝ≥0∞) {γ : ℝ} (hγ : 0 ≤ γ) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ logLogFactor q γ N :=
  one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (one_le_Lfun hN) (inv_nonneg.mpr ENNReal.toReal_nonneg))
    (Real.one_le_rpow (one_le_Ltwo hN) hγ)

lemma logLogFactor_mono (q : ℝ≥0∞) {γ : ℝ} (hγ : 0 ≤ γ) :
    MonotoneOn (logLogFactor q γ) (Ici 1) := by
  intro m hm n hn hmn
  exact mul_le_mul
    (Real.rpow_le_rpow (zero_le_one.trans (one_le_Lfun hm)) (Lfun_mono hm hn hmn)
      (inv_nonneg.mpr ENNReal.toReal_nonneg))
    (Real.rpow_le_rpow (zero_le_one.trans (one_le_Ltwo hm)) (Ltwo_mono hm hn hmn) hγ)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_Ltwo hm)) _)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_Lfun hn)) _)

/-- A série do fator de log-log converge exatamente quando `γq > 1`, para `γ ≥ 0`. -/
theorem logLog_dyadic_summable_iff {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    Summable (fun k : ℕ ↦ logLogFactor q γ (2 ^ (k + 1)) ^ (-q.toReal)) ↔ 1 < γ * q.toReal :=
  FormalizacaoIterated.iterated_factor_summable_iff hq hqt hγ 1

/-- Agenda `H⁽²⁾_{s;q,γ}` do artigo. -/
noncomputable def HlogLog (s : ℝ) (q : ℝ≥0∞) (γ : ℝ) : ℕ → ℕ :=
  Hregular s (logLogFactor q γ)

theorem logLog_schedule_iff {s : ℝ} (hs : 1 ≤ s) {q : ℝ≥0∞} (hq : 0 < q)
    (hqt : q ≠ ⊤) {γ : ℝ} (hγ : 0 ≤ γ) :
    lqNorm q (scheduleWeight s (HlogLog s q γ)) < ⊤ ↔ 1 < γ * q.toReal :=
  ((regular_schedule_criterion hs hq hqt (fun _ ↦ one_le_logLogFactor q hγ)
    (logLogFactor_mono q hγ)).1).trans (logLog_dyadic_summable_iff hq hqt hγ)

private lemma logLog_hypotheses {s : ℝ} (hs : 1 ≤ s) {q : ℝ≥0∞} (hq : 0 < q)
    (hqt : q ≠ ⊤) {γ : ℝ} (hγ : 1 / q.toReal < γ) :
    (∀ N : ℕ, 1 ≤ N → 8 * (N : ℝ) ^ max 1 s ≤ (HlogLog s q γ N : ℝ)) ∧
      lqNorm q (scheduleWeight s (HlogLog s q γ)) < ⊤ := by
  have hqR := ENNReal.toReal_pos hq.ne' hqt
  have hγ0 : 0 ≤ γ := (div_nonneg zero_le_one hqR.le).trans hγ.le
  refine ⟨fun N hN ↦ ?_, (logLog_schedule_iff hs hq hqt hγ0).mpr ((div_lt_iff₀ hqR).mp hγ)⟩
  rw [max_eq_right hs]
  exact (le_mul_of_one_le_right (by positivity) (one_le_logLogFactor q hγ0 hN)).trans
    (Hregular_lower (zero_le_one.trans hs) hN (one_le_logLogFactor q hγ0 hN))

/-- Corolário de log-log: caracterização com a biblioteca racional. -/
theorem conj1_loglog {p s : ℝ} (hp : 1 ≤ p) (hps : 1 / p < s) (hs : 1 ≤ s) (_hs2 : s < 2)
    {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) {γ : ℝ} (hγ : 1 / q.toReal < γ)
    {f : ℝ → ℝ} (hf : Measurable f) :
    f ∈ besovP (ENNReal.ofReal p) s q ↔
      f ∈ stratumP (ENNReal.ofReal p) s q (Pendencias.Agenda.Sigma (HlogLog s q γ)) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hl, hw⟩ := logLog_hypotheses hs hq hqt hγ
  exact ⟨besov_subset_stratum hp' (FormalizacaoJ.hypJp_of_lt hp hps) hq _ hl hw hf,
    stratum_subset_besov_conn hp' _ (fun _ _ ↦ measurable_sigma) s q hq hf⟩

/-- Estabilidade por inclusão com a mesma agenda de log-log. -/
theorem conj2_loglog {p s : ℝ} (hp : 1 ≤ p) (hps : 1 / p < s) (hs : 1 ≤ s) (_hs2 : s < 2)
    {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) {γ : ℝ} (hγ : 1 / q.toReal < γ) (c : ℝ) :
    Conj2Stability (ENNReal.ofReal p) s q (HlogLog s q γ) c := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hl, hw⟩ := logLog_hypotheses hs hq hqt hγ
  intro hc F h0 hnest hm hcont f hf
  exact FormalizacaoStab.stability_iff_of_J hp' (FormalizacaoJ.hypJp_of_lt hp hps) hq _
    hl hw F h0 hnest hm hc hcont hf

/-- Estabilidade por inclusão aproximada com a mesma agenda de log-log. -/
theorem conj2_approx_loglog {p s : ℝ} (hp : 1 ≤ p) (hps : 1 / p < s) (hs : 1 ≤ s) (_hs2 : s < 2)
    {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) {γ : ℝ} (hγ : 1 / q.toReal < γ)
    (c : ℝ) (ε : ℕ → ℝ≥0∞) :
    Conj2ApproxStability (ENNReal.ofReal p) s q (HlogLog s q γ) c ε := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hl, hw⟩ := logLog_hypotheses hs hq hqt hγ
  intro hc hEps F h0 hnest hm hcont f hf
  exact FormalizacaoStab.stability_approx_iff_of_J hp' (FormalizacaoJ.hypJp_of_lt hp hps) hq _
    hl hw F h0 hnest hm hc hEps hcont hf


private lemma logLog_quantWeight_lt_top {s : ℝ} (hs : 1 ≤ s) {q : ℝ≥0∞} (hq : 0 < q)
    (hqt : q ≠ ⊤) {γ : ℝ} (hγ : 0 ≤ γ) (hγq : 1 < γ * q.toReal) :
    lqNorm q (quantWeight s (qexp s (logLogFactor q γ))) < ⊤ := by
  let h := logLogFactor q γ
  have hh (r : ℕ) : 1 ≤ h (2 ^ r) := one_le_logLogFactor q hγ Nat.one_le_two_pow
  have hfin : lqNorm q (fun k : ℕ ↦ ENNReal.ofReal ((h (2 ^ (k + 1)))⁻¹)) < ⊤ := by
    apply (lq_ofReal_iff hq hqt (fun k ↦ inv_nonneg.mpr (zero_le_one.trans (hh (k + 1))))).mpr
    have he (k : ℕ) : ((h (2 ^ (k + 1)))⁻¹) ^ q.toReal = h (2 ^ (k + 1)) ^ (-q.toReal) := by
      rw [Real.inv_rpow (zero_le_one.trans (hh _)), Real.rpow_neg (zero_le_one.trans (hh _))]
    simpa only [he] using (logLog_dyadic_summable_iff hq hqt hγ).mpr hγq
  refine (lq_mono hq fun k ↦ ?_).trans_lt hfin
  let r := k + 1
  have hQ := (qexp_spec hs hh r).2.1
  change quantWeight s (qexp s h) k ≤ ENNReal.ofReal ((h (2 ^ r))⁻¹)
  rw [quantWeight, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  change (2 : ℝ) ^ ((r : ℝ) * s) * (1 / (2 * 2 ^ qexp s h r)) ≤ (h (2 ^ r))⁻¹
  rw [← Real.rpow_natCast (2 : ℝ) r, ← Real.rpow_mul (by norm_num)] at hQ
  rw [← div_eq_mul_one_div, ← one_div,
    div_le_div_iff₀ (by positivity) (zero_lt_one.trans_le (hh r)), one_mul]
  exact hQ.trans (le_mul_of_one_le_left (by positivity) (by norm_num))

/-- Agenda de log-log uniforme sobre uma bola de raio `B`. -/
noncomputable def HlogLogBall (A B s : ℝ) (q : ℝ≥0∞) (γ : ℝ) (N : ℕ) : ℕ :=
  ⌈A * (B + 1) * ((N : ℝ) + 1) ^ s * logLogFactor q γ N⌉₊

private lemma logLog_ball_budget {p s : ℝ} (hps : 1 / p < s) (hs : 1 ≤ s) {q : ℝ≥0∞}
    {γ Cs B : ℝ} (hγ : 0 ≤ γ) (hCs : 1 ≤ Cs) (hB : 1 ≤ B) (r : ℕ) :
    8 * (Cs * B * LamU p s q r + 1) * 2 ^ qexp s (logLogFactor q γ) r ≤
      (HlogLogBall (32 * (Cs + 1)) B s q γ (2 ^ r) : ℝ) := by
  let h := logLogFactor q γ
  have hh (r : ℕ) : 1 ≤ h (2 ^ r) := one_le_logLogFactor q hγ Nat.one_le_two_pow
  rw [LamU, if_pos hps, mul_one]
  have hQ := (qexp_spec hs hh r).2.2
  have hc : 8 * (Cs * B + 1) * 2 ≤ 32 * (Cs + 1) * (B + 1) := by nlinarith
  have hn : ((2 : ℝ) ^ r) ^ s ≤ ((2 : ℝ) ^ r + 1) ^ s :=
    Real.rpow_le_rpow (by positivity) (le_add_of_nonneg_right zero_le_one) (zero_le_one.trans hs)
  calc _ ≤ 8 * (Cs * B + 1) * (2 * (((2 : ℝ) ^ r) ^ s * h (2 ^ r))) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = 8 * (Cs * B + 1) * 2 * (((2 : ℝ) ^ r) ^ s * h (2 ^ r)) := by ring
    _ ≤ (32 * (Cs + 1)) * (B + 1) * (((2 : ℝ) ^ r + 1) ^ s * h (2 ^ r)) :=
      mul_le_mul hc (mul_le_mul_of_nonneg_right hn (zero_le_one.trans (hh r)))
        (mul_nonneg (by positivity) (zero_le_one.trans (hh r))) (by positivity)
    _ ≤ _ := by
      apply le_trans _ (Nat.le_ceil _)
      push_cast
      change _ ≤ 32 * (Cs + 1) * (B + 1) * (((2 : ℝ) ^ r + 1) ^ s) * h (2 ^ r)
      ring_nf
      exact le_rfl

/-- Corolário de log-log, versão quantitativa uniforme do Teorema 6.3. -/
theorem uniform_loglog_ball {p s : ℝ} (hp : 1 ≤ p) (hps : 1 / p < s) (hs : 1 ≤ s) (_hs2 : s < 2)
    {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) :
    ∃ CW Cs : ℝ, 0 ≤ CW ∧ 1 ≤ Cs ∧ ∀ γ : ℝ, 1 / q.toReal < γ →
      (∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
        besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
        ∀ r, 1 ≤ r →
          let H := HlogLogBall (32 * (Cs + 1)) B s q γ
          let Q : ℝ := 2 ^ qexp s (logLogFactor q γ) r
          let E := 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
            ENNReal.ofReal (1 / (2 * Q))
          ∃ g ∈ classNH (2 ^ r) (H (2 ^ r)), distP (ENNReal.ofReal p) f g ≤ E ∧
            E ≤ ENNReal.ofReal ((9 * CW * B + 1) * ((2 : ℝ) ^ r) ^ (-s)) ∧
            realP (ENNReal.ofReal p) (Pendencias.Agenda.Sigma H) (2 ^ r) f ≤
              ENNReal.ofReal (((1 + 45 * CW) * B + 5 / 2) * ((2 : ℝ) ^ r) ^ (-s))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 1 ≤ B → ∀ f : ℝ → ℝ, Measurable f →
        besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
        lqNorm q (stratSeq (ENNReal.ofReal p) s
          (Pendencias.Agenda.Sigma (HlogLogBall (32 * (Cs + 1)) B s q γ)) f) ≤
          ENNReal.ofReal (C * (B + 1)) := by
  obtain ⟨CW, Cs, hCW, hCs, hunif⟩ := uniform_ball_of_budget (s := s) hp hq
  refine ⟨CW, Cs, hCW, hCs, fun γ hγ ↦ ?_⟩
  have hqR := ENNReal.toReal_pos hq.ne' hqt
  have hγ₀ := (div_nonneg zero_le_one hqR.le).trans hγ.le
  have hh (r : ℕ) : 1 ≤ logLogFactor q γ (2 ^ r) := one_le_logLogFactor q hγ₀ Nat.one_le_two_pow
  obtain ⟨happ, hrate⟩ := hunif
    (qexp s (logLogFactor q γ)) (fun Cs B ↦ HlogLogBall (32 * (Cs + 1)) B s q γ)
    (fun r _ ↦ (qexp_spec hs hh r).1) (fun r _ ↦ qexp_s_le hs le_rfl hh r)
    (fun _ hB r _ ↦ logLog_ball_budget hps hs hγ₀ hCs hB r)
  exact ⟨happ,
    hrate (logLog_quantWeight_lt_top hs hq hqt hγ₀ ((div_lt_iff₀ hqR).mp hγ))⟩


private noncomputable def diagonalFactor (q : ℝ≥0∞) (γ : ℝ) (N : ℕ) : ℝ :=
  Lfun N ^ thetaQ q * logLogFactor q γ N

/-- Agenda de log-log na diagonal `p = s = 1`, incluindo o fator `L₁^θ_q`. -/
noncomputable def HlogLogDiag (q : ℝ≥0∞) (γ : ℝ) : ℕ → ℕ :=
  Hregular 1 (diagonalFactor q γ)

lemma HlogLogDiag_eq (q : ℝ≥0∞) (γ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    HlogLogDiag q γ N =
      ⌈8 * ((N : ℝ) + 1) * Lfun N ^ (thetaQ q + q.toReal⁻¹) * Ltwo N ^ γ⌉₊ := by
  unfold HlogLogDiag Hregular diagonalFactor logLogFactor
  rw [Real.rpow_one, Real.rpow_add (zero_lt_one.trans_le (one_le_Lfun hN))]
  congr 1
  ring

private lemma diagonalFactor_mono (q : ℝ≥0∞) {γ : ℝ} (hγ : 0 ≤ γ) :
    MonotoneOn (diagonalFactor q γ) (Ici 1) := by
  intro a ha b hb hab
  have h₁ := zero_le_one.trans (one_le_Lfun ha)
  have h₂ := zero_le_one.trans (one_le_Lfun hb)
  exact mul_le_mul (Real.rpow_le_rpow h₁ (Lfun_mono ha hb hab) (thetaQ_nonneg q))
    (logLogFactor_mono q hγ ha hb hab)
    (zero_le_one.trans (one_le_logLogFactor q hγ ha)) (Real.rpow_nonneg h₂ _)

private lemma diagonalFactor_ge (q : ℝ≥0∞) {γ : ℝ} (hγ : 0 ≤ γ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ diagonalFactor q γ n :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (one_le_Lfun hn) (thetaQ_nonneg q))
    (one_le_logLogFactor q hγ hn)

private lemma HlogLogDiag_mono {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤)
    {γ : ℝ} (hγ : 0 ≤ γ) : Monotone (HlogLogDiag q γ) := by
  intro n m hnm
  by_cases hn : n = 0
  · subst n
    have he : q.toReal⁻¹ ≠ 0 := inv_ne_zero (ENNReal.toReal_pos hq.ne' hqt).ne'
    have hz : HlogLogDiag q γ 0 = 0 := by
      simp [HlogLogDiag, Hregular, diagonalFactor, logLogFactor, Lfun, Real.zero_rpow he]
    simp [hz]
  · have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hm₁ := hn₁.trans hnm
    apply Nat.ceil_mono
    simp only [Real.rpow_one]
    exact mul_le_mul (by gcongr) (diagonalFactor_mono q hγ hn₁ hm₁ hnm)
      (zero_le_one.trans (diagonalFactor_ge q hγ hn₁)) (by positivity)

private lemma diagonal_logLog_shift (q : ℝ≥0∞) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∀ K : ℝ, 1 ≤ K → ∃ e₀ : ℕ, ∀ r : ℕ, 1 ≤ r →
      8 * (K * Lam 1 1 q r + 1) * 2 ^ qexp 1 (logLogFactor q γ) r ≤
        (HlogLogDiag q γ (2 ^ (r + e₀)) : ℝ) := by
  intro K hK
  let e₀ : ℕ := ⌈4 * (K + 1)⌉₊
  refine ⟨e₀, fun r hr ↦ ?_⟩
  let θ := thetaQ q
  let h := logLogFactor q γ
  have hh (i : ℕ) : 1 ≤ h (2 ^ i) := one_le_logLogFactor q hγ Nat.one_le_two_pow
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hΛ : Lam 1 1 q r = (r : ℝ) ^ θ := by simp [Lam, θ]
  have hθ := thetaQ_nonneg q
  have hrθ := Real.one_le_rpow hr₁ hθ
  have hL := one_le_Lfun (N := 2 ^ r) Nat.one_le_two_pow
  have hrL : (r : ℝ) ≤ 2 * Lfun (2 ^ r) := by
    rw [Lfun_two_pow]
    nlinarith [Real.log_two_gt_d9]
  have hθbound : (r : ℝ) ^ θ ≤ 2 * Lfun (2 ^ r) ^ θ := by
    calc _ ≤ (2 * Lfun (2 ^ r)) ^ θ := Real.rpow_le_rpow (by positivity) hrL hθ
      _ = (2 : ℝ) ^ θ * Lfun (2 ^ r) ^ θ :=
        Real.mul_rpow (by norm_num) (zero_le_one.trans hL)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (thetaQ_le_one q))
        (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hKθ : K * (r : ℝ) ^ θ + 1 ≤ (K + 1) * (r : ℝ) ^ θ := by linarith
  have hQ := (qexp_spec (ν := 1) le_rfl hh r).2.2
  rw [Real.rpow_one] at hQ
  have hN : 4 * (K + 1) ≤ (2 : ℝ) ^ e₀ :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.lt_two_pow_self (n := e₀)).le)
  have hfac := diagonalFactor_mono q hγ (a := 2 ^ r) (b := 2 ^ (r + e₀))
    Nat.one_le_two_pow Nat.one_le_two_pow (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hΛ]
  calc _ ≤ 8 * ((K + 1) * (2 * Lfun (2 ^ r) ^ θ)) * (2 * ((2 : ℝ) ^ r * h (2 ^ r))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hKθ.trans
        (mul_le_mul_of_nonneg_left hθbound (by positivity))) (by norm_num)) hQ
        (by positivity) (by positivity)
    _ = 8 * ((2 : ℝ) ^ r * (4 * (K + 1))) * diagonalFactor q γ (2 ^ r) := by
        unfold diagonalFactor
        change _ = 8 * ((2 : ℝ) ^ r * (4 * (K + 1))) * (Lfun (2 ^ r) ^ θ * h (2 ^ r))
        ring
    _ ≤ 8 * ((2 : ℝ) ^ (r + e₀)) * diagonalFactor q γ (2 ^ (r + e₀)) := by
        rw [pow_add]
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ (2 : ℝ) ^ r)) (by norm_num)) hfac
          (zero_le_one.trans (diagonalFactor_ge q hγ Nat.one_le_two_pow)) (by positivity)
    _ ≤ _ := by
      have h := Hregular_lower (s := 1) zero_le_one (N := 2 ^ (r + e₀)) Nat.one_le_two_pow
        (diagonalFactor_ge q hγ Nat.one_le_two_pow)
      simpa only [HlogLogDiag, Real.rpow_one, Nat.cast_pow, Nat.cast_ofNat] using h

/-- A agenda com log-log caracteriza também o caso `p = s = 1` da Observação 6.13. -/
theorem conj1_loglog_diagonal {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤)
    {γ : ℝ} (hγ : 1 / q.toReal < γ) {f : ℝ → ℝ} (hf : Measurable f) :
    f ∈ besovP 1 1 q ↔ f ∈ stratumP 1 1 q (Pendencias.Agenda.Sigma (HlogLogDiag q γ)) := by
  have hqR := ENNReal.toReal_pos hq.ne' hqt
  have hγ₀ := (div_nonneg zero_le_one hqR.le).trans hγ.le
  let h := logLogFactor q γ
  let m : ℕ → ℕ := fun r ↦ qexp 1 h r - r
  have he (r : ℕ) : r + m r = qexp 1 h r := Nat.add_sub_of_le
    ((qexp_spec (ν := 1) le_rfl (fun _ ↦ one_le_logLogFactor q hγ₀ Nat.one_le_two_pow) r).1)
  obtain ⟨h0, hnest, hm, hcont⟩ := sigma_family (HlogLogDiag_mono hq hqt hγ₀)
  refine ⟨fun hbes ↦ ?_, stratum_subset_besov_conn le_rfl _ hm 1 q hq hf⟩
  have hw := logLog_quantWeight_lt_top (s := 1) le_rfl hq hqt hγ₀ ((div_lt_iff₀ hqR).mp hγ)
  have hs (K : ℝ) (hK : 1 ≤ K) : ∃ e₀ : ℕ, ∀ r : ℕ, 1 ≤ r →
      8 * (K * Lam 1 1 q r + 1) * 2 ^ (r + m r) ≤ (HlogLogDiag q γ (2 ^ (r + e₀)) : ℝ) := by
    simp_rw [he]
    exact diagonal_logLog_shift q hγ₀ K hK
  have hrate := besov_subset_stratum_low (p := 1) (s := 1) le_rfl (by norm_num)
    hq (HlogLogDiag q γ) m hs (by simpa only [he, quantWeight] using hw)
    _ h0 hnest le_rfl hcont hf
  have hbes' : f ∈ besovP (ENNReal.ofReal 1) 1 q := by simpa using hbes
  simpa only [ENNReal.ofReal_one] using hrate hbes'


open Filter Asymptotics
open scoped Topology

private lemma Lfun_tendsto_atTop : Tendsto Lfun atTop atTop := by
  have h : Tendsto (fun N : ℕ ↦ Real.exp 1 * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos _)
  exact Real.tendsto_log_atTop.comp h

/-- Para todo expoente simples `κ > 1/q`, a razão entre as agendas tende a zero. -/
theorem logLog_schedule_ratio_tendsto_zero {s γ κ : ℝ} (hs : 1 ≤ s) (hγ : 0 ≤ γ)
    (q : ℝ≥0∞) (hκ : q.toReal⁻¹ < κ) :
    Tendsto (fun N : ℕ ↦ (HlogLog s q γ N : ℝ) / (Pendencias.Agenda.Hsk s κ N : ℝ))
      atTop (𝓝 0) := by
  let δ := κ - q.toReal⁻¹
  have hδ : 0 < δ := sub_pos.mpr hκ
  have hAsymp : Tendsto (fun x : ℝ ↦ (Real.log x) ^ γ / x ^ δ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop γ hδ).tendsto_div_nhds_zero
  have hAsymp' : Tendsto (fun N : ℕ ↦ (2 : ℝ) ^ γ *
      ((Real.log (Lfun N)) ^ γ / Lfun N ^ δ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hAsymp.comp Lfun_tendsto_atTop).const_mul ((2 : ℝ) ^ γ)
  have hdom : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (Lfun N) :=
    (Real.tendsto_log_atTop.comp Lfun_tendsto_atTop).eventually_ge_atTop 1
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ div_nonneg (by positivity) (by positivity))
    _ (by simpa only [mul_zero] using hAsymp'.const_mul (2 : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hdom] with N hN hlog
  have hL := one_le_Lfun hN
  have hbase : 0 < (8 : ℝ) * ((N : ℝ) + 1) ^ s := by positivity
  have hfactor := one_le_logLogFactor q hγ hN
  have h₁ : (HlogLog s q γ N : ℝ) ≤
      2 * (8 * ((N : ℝ) + 1) ^ s * logLogFactor q γ N) := by
    have hx : 1 ≤ 8 * ((N : ℝ) + 1) ^ s * logLogFactor q γ N := by
      have ha := Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg N)) (zero_le_one.trans hs)
      nlinarith [one_le_mul_of_one_le_of_one_le ha hfactor]
    have h : (HlogLog s q γ N : ℝ) <
        8 * ((N : ℝ) + 1) ^ s * logLogFactor q γ N + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have h₂ : 8 * ((N : ℝ) + 1) ^ s * Lfun N ^ κ ≤ (Pendencias.Agenda.Hsk s κ N : ℝ) := by
    simpa only [max_eq_right hs, Lfun] using FormalizacaoSched.Hsk_real_ge s κ N
  have hden : 0 < (8 : ℝ) * ((N : ℝ) + 1) ^ s * Lfun N ^ κ :=
    mul_pos hbase (Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _)
  have hf : Ltwo N ^ γ ≤ (2 : ℝ) ^ γ * Real.log (Lfun N) ^ γ := by
    rw [← Real.mul_rpow (by norm_num) (zero_le_one.trans hlog)]
    exact Real.rpow_le_rpow (zero_le_one.trans (one_le_Ltwo hN)) (by unfold Ltwo; linarith) hγ
  calc (HlogLog s q γ N : ℝ) / (Pendencias.Agenda.Hsk s κ N : ℝ)
      ≤ (2 * (8 * ((N : ℝ) + 1) ^ s * logLogFactor q γ N)) /
          (8 * ((N : ℝ) + 1) ^ s * Lfun N ^ κ) :=
        div_le_div_of_nonneg_right h₁ (hden.trans_le h₂).le |>.trans
          (div_le_div_of_nonneg_left (by positivity) hden h₂)
    _ = 2 * (Ltwo N ^ γ / Lfun N ^ δ) := by
      have he : Lfun N ^ κ = Lfun N ^ q.toReal⁻¹ * Lfun N ^ δ := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hL)]
        congr 1
        dsimp [δ]
        ring
      rw [he, logLogFactor]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hf (Real.rpow_nonneg (zero_le_one.trans hL) _)

end FormalizacaoLogLog
