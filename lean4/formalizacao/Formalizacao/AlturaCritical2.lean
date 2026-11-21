import Formalizacao.AlturaCritical
import Formalizacao.LqLemmas

/-!
# Altura linear crítica: cotas de realização e de `ℓ^q` (auditoria, Parte V)

A partir de `critical_approx`, obtemos para cada nível `N = 2^r` um aproximante `T ∈ A_{N,H}` com
`R_N(f) ≤ ω(f,1/N) + 5(9 C_W ω(f,1/N) + 8(M+1)/H)`. Aqui se prova essa cota (`critical_level`),
a cota `B₀ ≤ C₀B` e a cota `2^{k/p} Wr(2^k) ≤ B` a partir da norma de Besov.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoCrit2

open FormalizacaoCrit FormalizacaoLp FormalizacaoLow FormalizacaoRed FormalizacaoFloor Artigo
open FormalizacaoGrid FormalizacaoQuasi FormalizacaoL55 FormalizacaoL55b FormalizacaoCor

/-- Termo de uma sequência é limitado pela norma `ℓ^q` (para `0 < q`). -/
lemma term_le_lqNorm {q : ℝ≥0∞} (hq : 0 < q) (a : ℕ → ℝ≥0∞) (k : ℕ) :
    a k ≤ lqNorm q a := by
  unfold lqNorm
  split_ifs with hqt
  · exact le_iSup a k
  · have hQ : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hle : a k ^ q.toReal ≤ ∑' r, a r ^ q.toReal := ENNReal.le_tsum (f := fun r => a r ^ q.toReal) k
    calc a k = (a k ^ q.toReal) ^ q.toReal⁻¹ := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hQ.ne', ENNReal.rpow_one]
      _ ≤ (∑' r, a r ^ q.toReal) ^ q.toReal⁻¹ :=
          ENNReal.rpow_le_rpow hle (inv_nonneg.mpr hQ.le)

/-- A norma de Besov controla `2^{k/p} Wr(2^k)` para `k ≥ 1`. -/
lemma wr_le_of_besov {q : ℝ≥0∞} (hq : 0 < q) {p' : ℝ} (hp1 : 1 ≤ p') {f : ℝ → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbes : besovNorm (ENNReal.ofReal p') (1 / p') q f ≤ ENNReal.ofReal B)
    (hfin : Np p' f (Icc 0 1) < ⊤) (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) * (1 / p')) * Wr p' f (2 ^ k) ≤ B := by
  have hterm := (term_le_lqNorm hq (besovSeq (ENNReal.ofReal p') (1 / p') f) k).trans
    ((lqNorm_le_besovNorm _ _ _ f).trans hbes)
  unfold besovSeq at hterm
  have hwfin : wtP (ENNReal.ofReal p') (1 / (2 : ℝ) ^ k) f < ⊤ := by
    have := wtP_lt_top hp1 hf hfin (2 ^ k)
    simpa [Nat.cast_pow] using this
  have ha : (0 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * (1 / p')) := by positivity
  have hfin2 : ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) * (1 / p'))) *
      wtP (ENNReal.ofReal p') (1 / (2 : ℝ) ^ k) f ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwfin.ne
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hterm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hB] at hreal
  have hWr : Wr p' f (2 ^ k) = (wtP (ENNReal.ofReal p') (1 / (2 : ℝ) ^ k) f).toReal := by
    unfold Wr; simp [Nat.cast_pow]
  rw [hWr]
  exact hreal

/-- `B₀ ≤ C₀ B` a partir da norma de Besov (com `Np ≤ B` e o primeiro nível `≤ B`). -/
lemma B0_le {p CW B : ℝ} (hp : 1 ≤ p) (hCW : 0 ≤ CW) {f : ℝ → ℝ} (hf : Measurable f)
    (hfin : Np p f (Icc 0 1) < ⊤) (hB : 0 ≤ B)
    (hNp : (Np p f (Icc 0 1)).toReal ≤ B)
    (hW2 : (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal ≤ B) :
    B0 p CW f ≤ 8 * (2 : ℝ) ^ (1 / p) * (1 + 9 * CW) * B := by
  have hw : wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f < ⊤ := by
    have := wtP_lt_top hp hf hfin 2
    simpa using this
  have hZ : (9 : ℝ≥0∞) * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hw.ne
  have hsum : (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal =
      (Np p f (Icc 0 1)).toReal + 9 * CW *
        (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal := by
    rw [ENNReal.toReal_add hfin.ne hZ, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hCW]
    simp
  have hpow : (1 / (2 : ℝ)) ^ (-(1 / p)) = (2 : ℝ) ^ (1 / p) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  unfold B0
  rw [hpow, hsum]
  have h2 : (0 : ℝ) ≤ 8 * (2 : ℝ) ^ (1 / p) := by positivity
  have hfin3 : (Np p f (Icc 0 1)).toReal + 9 * CW * (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal
      ≤ B + 9 * CW * B := by
    have := mul_le_mul_of_nonneg_left hW2 (by positivity : (0 : ℝ) ≤ 9 * CW)
    linarith
  calc 8 * (2 : ℝ) ^ (1 / p) * ((Np p f (Icc 0 1)).toReal + 9 * CW *
        (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal)
      ≤ 8 * (2 : ℝ) ^ (1 / p) * (B + 9 * CW * B) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 8 * (2 : ℝ) ^ (1 / p) * (1 + 9 * CW) * B := by ring

/-- Erro em `L^p` do aproximante construído por `critical_approx`. -/
theorem critical_dist {p CW : ℝ} (hp : 1 < p) (hW : FormalizacaoCor.WhitneyLp p CW)
    (hCW : 0 ≤ CW) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hWB : ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤ B)
    {r : ℕ} (hr : 1 ≤ r) {H : ℕ}
    (hH1 : 8 * (2 : ℝ) ^ r ≤ H)
    (hH2 : 16 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r + 1) ≤ H)
    (hH3 : (2 : ℝ) ^ r * (4 * B0 p CW f + 288 * CW * (2 : ℝ) ^ (1 / p) * B + 1) ≤ H) :
    ∃ T : LTree, AdmNH (2 ^ r) H T ∧
      distP (ENNReal.ofReal p) f (T.eval 0 0) ≤
        9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / ((2 ^ r : ℕ) : ℝ)) f +
          ENNReal.ofReal (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r + 1) / H) := by
  obtain ⟨T, hT, hbound⟩ := critical_approx hp hW hCW hf hfi hfin hB hWB hr hH1 hH2 hH3
  have hTmem : T.eval 0 0 ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) (2 ^ r) := by
    simp only [Pendencias.Agenda.Sigma, Set.mem_setOf_eq]
    exact Or.inr ⟨T, hT, rfl⟩
  have hTm : Measurable (T.eval 0 0) := FormalizacaoLp.measurable_sigma hTmem
  have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  have hn2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have hQq := FormalizacaoCor.quasi_error hp.le hW hn2 hf hfi hfin
  have hQc : Continuous (Q (2 ^ r) f) := FormalizacaoL55.Q_continuous (2 ^ r) f
  refine ⟨T, hT, ?_⟩
  unfold distP
  have hsplit : f - T.eval 0 0 = (fun x ↦ f x - Q (2 ^ r) f x) +
      (fun x ↦ Q (2 ^ r) f x - T.eval 0 0 x) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  have hm1 : AEStronglyMeasurable (fun x ↦ f x - Q (2 ^ r) f x) (volume.restrict (Icc 0 1)) :=
    (hf.sub hQc.measurable).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x ↦ Q (2 ^ r) f x - T.eval 0 0 x)
      (volume.restrict (Icc 0 1)) :=
    (hQc.measurable.sub hTm).aestronglyMeasurable
  refine (eLpNorm_add_le hm1 hm2 hp1').trans (add_le_add hQq ?_)
  refine (eLpNorm_le_of_ae_bound
    (C := 8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r + 1) / H) ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs]
    exact hbound x hx
  · simp [Real.volume_Icc]

/-- **Cota de realização de um nível crítico.** Para `H` com as três condições de
`critical_approx`, `R_N^H(f) ≤ ω + 5(9 C_W ω + 8(M+1)/H)` com `ω = ω_p(f,1/N)`, `N = 2^r`. -/
theorem critical_level {p CW : ℝ} (hp : 1 < p) (hW : FormalizacaoCor.WhitneyLp p CW)
    (hCW : 0 ≤ CW) {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hWB : ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤ B)
    {r : ℕ} (hr : 1 ≤ r) {H : ℕ}
    (hH1 : 8 * (2 : ℝ) ^ r ≤ H)
    (hH2 : 16 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r + 1) ≤ H)
    (hH3 : (2 : ℝ) ^ r * (4 * B0 p CW f + 288 * CW * (2 : ℝ) ^ (1 / p) * B + 1) ≤ H) :
    realP (ENNReal.ofReal p) (fun M ↦ Pendencias.Agenda.Sigma (fun _ ↦ H) M) (2 ^ r) f ≤
      wtP (ENNReal.ofReal p) (1 / ((2 ^ r : ℕ) : ℝ)) f +
        5 * (9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / ((2 ^ r : ℕ) : ℝ)) f +
          ENNReal.ofReal (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * r + 1) / H)) := by
  obtain ⟨T, hT, hdist⟩ := critical_dist hp hW hCW hf hfi hfin hB hWB hr hH1 hH2 hH3
  have hTmem : T.eval 0 0 ∈ Pendencias.Agenda.Sigma (fun _ ↦ H) (2 ^ r) := by
    simp only [Pendencias.Agenda.Sigma, Set.mem_setOf_eq]
    exact Or.inr ⟨T, hT, rfl⟩
  have hTm : Measurable (T.eval 0 0) := FormalizacaoLp.measurable_sigma hTmem
  have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  have hr' := FormalizacaoAltura.realP_le_of_member hp1' (fun M ↦ Pendencias.Agenda.Sigma (fun _ ↦ H) M) (2 ^ r)
    hf hTmem hTm
  refine hr'.trans ?_
  exact add_le_add le_rfl (mul_le_mul_left' hdist 5)

end FormalizacaoCrit2
