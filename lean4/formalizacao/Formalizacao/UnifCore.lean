import Formalizacao.UnifSup
import Formalizacao.LowTransfer

/-!
# Seção 6, parte 3: núcleo abstrato das cotas uniformes

* `qexp ν h r = ⌈ν r + log₂ h(2^r)⌉`: o expoente `e` de `Q(n) = 2^e`, a menor potência de dois
  `≥ n^ν h(n)` (`qexp_spec`).
* `unif_core`: para `f` na bola de raio `B`, se `e` e a agenda `H` satisfazem
  `8 (C B Λ_r + 1) 2^{e r} ≤ H(2^r)`, então há `g ∈ A_{2^r,H(2^r)}` com erro
  `9 C_W ω_p(f,2^{-r}) + 1/(2·2^{e r})`, e `R_{2^r}(f) ≤ ω + 5 D`.
* `unif_rate`: a sequência de realização está em `ℓ^q` com norma `≲ B + c`, desde que a
  sequência `2^{(k+1)s} · 1/(2·2^{e(k+1)})` tenha norma `ℓ^q` finita.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoLp FormalizacaoRed FormalizacaoLq

namespace FormalizacaoLow

/-- Expoente de quantização `⌈ν r + log₂ h(2^r)⌉`. -/
noncomputable def qexp (ν : ℝ) (h : ℕ → ℝ) (r : ℕ) : ℕ :=
  ⌈ν * (r : ℝ) + Real.logb 2 (h (2 ^ r))⌉₊

lemma qexp_spec {ν : ℝ} (hν : 1 ≤ ν) {h : ℕ → ℝ} (hh : ∀ r, 1 ≤ h (2 ^ r)) (r : ℕ) :
    r ≤ qexp ν h r ∧
    ((2 : ℝ) ^ r) ^ ν * h (2 ^ r) ≤ (2 : ℝ) ^ (qexp ν h r) ∧
    (2 : ℝ) ^ (qexp ν h r) ≤ 2 * (((2 : ℝ) ^ r) ^ ν * h (2 ^ r)) := by
  have hlog : 0 ≤ Real.logb 2 (h (2 ^ r)) := Real.logb_nonneg (by norm_num) (hh r)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hx : (r : ℝ) ≤ ν * (r : ℝ) + Real.logb 2 (h (2 ^ r)) := by nlinarith
  have hpos : 0 < h (2 ^ r) := lt_of_lt_of_le one_pos (hh r)
  have h2x : (2 : ℝ) ^ (ν * (r : ℝ) + Real.logb 2 (h (2 ^ r))) =
      ((2 : ℝ) ^ r) ^ ν * h (2 ^ r) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hpos,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (r : ℝ) ν]
  refine ⟨?_, ?_, ?_⟩
  · have : (r : ℝ) ≤ (qexp ν h r : ℝ) := hx.trans (Nat.le_ceil _)
    exact_mod_cast this
  · calc ((2 : ℝ) ^ r) ^ ν * h (2 ^ r)
        = (2 : ℝ) ^ (ν * (r : ℝ) + Real.logb 2 (h (2 ^ r))) := h2x.symm
      _ ≤ (2 : ℝ) ^ ((qexp ν h r : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = (2 : ℝ) ^ (qexp ν h r) := Real.rpow_natCast _ _
  · have hlt : ((qexp ν h r : ℕ) : ℝ) < ν * (r : ℝ) + Real.logb 2 (h (2 ^ r)) + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    calc (2 : ℝ) ^ (qexp ν h r) = (2 : ℝ) ^ ((qexp ν h r : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (ν * (r : ℝ) + Real.logb 2 (h (2 ^ r)) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
      _ = 2 * (((2 : ℝ) ^ r) ^ ν * h (2 ^ r)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, h2x]; ring

/-- **Núcleo uniforme.** -/
theorem unif_core {p : ℝ} (hp : 1 ≤ p) {s : ℝ} {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ CW Cs : ℝ, 0 ≤ CW ∧ 1 ≤ Cs ∧ ∀ B : ℝ, 1 ≤ B → ∀ (e H : ℕ → ℕ),
      (∀ r, 1 ≤ r → r ≤ e r) →
      (∀ r, 1 ≤ r → 8 * (Cs * B * LamU p s q r + 1) * 2 ^ (e r) ≤ (H (2 ^ r) : ℝ)) →
      ∀ f : ℝ → ℝ, Measurable f → besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
        ∀ r, 1 ≤ r → ∃ g ∈ classNH (2 ^ r) (H (2 ^ r)),
          eLpNorm (f - g) (ENNReal.ofReal p) vol01 ≤
            9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
              ENNReal.ofReal (1 / (2 * 2 ^ (e r))) ∧
          realP (ENNReal.ofReal p) (Pendencias.Agenda.Sigma H) (2 ^ r) f ≤
            wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
              5 * (9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
                ENNReal.ofReal (1 / (2 * 2 ^ (e r)))) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨CW, hCW, hq'⟩ := FormalizacaoW.quasi_error_unc hp
  obtain ⟨Cs, hCs1, hCs⟩ := lam_bound_unif (p := p) (s := s) hp hq
  refine ⟨CW, Cs, hCW, hCs1, fun B hB e H hre hH f hf hball r hr => ?_⟩
  obtain ⟨hN1, _, _, hfin, _, _⟩ := ball_bounds hp hq (by linarith) hf hball
  have hfi : IntegrableOn f (Icc 0 1) := by
    have hmem : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨hf.aestronglyMeasurable, hfin⟩
    exact hmem.integrable hp1
  have hL : 1 ≤ LamU p s q r := one_le_LamU p s q hr
  have hM : 0 ≤ Cs * B * LamU p s q r := by positivity
  have hr2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  obtain ⟨g, hg, hD⟩ := FormalizacaoJ.lp_jackson_low_core hp hq' hf hfi hfin hM hr2 (hre r hr)
    (fun j hj => hCs B hB f hf hball r hr j hj) (hH r hr)
  refine ⟨g, hg, hD, ?_⟩
  have hgS : g ∈ Pendencias.Agenda.Sigma H (2 ^ r) := classNH_subset_sigma H (2 ^ r) hg
  have hR := realP_le_of_approx hp1 hf hgS hD
  have hcast : ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r := by push_cast; rfl
  rw [hcast] at hR
  exact hR

/-- Peso, indexado a partir de `r = 1`, do erro de arredondamento `1/(2Q)`. -/
noncomputable def quantWeight (s : ℝ) (e : ℕ → ℕ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
    ENNReal.ofReal (1 / (2 * 2 ^ (e (k + 1))))

/-- Passagem da cota por escala para a norma da sequência de realização. -/
theorem unif_rate_of_scale {p : ℝ≥0∞} {s : ℝ} {q : ℝ≥0∞} (hq : 0 < q)
    {CW B : ℝ} {e H : ℕ → ℕ} {f : ℝ → ℝ}
    (hball : besovNorm p s q f ≤ ENNReal.ofReal B)
    (hscale : ∀ r, 1 ≤ r →
      realP p (Pendencias.Agenda.Sigma H) (2 ^ r) f ≤
        wtP p (1 / (2 : ℝ) ^ r) f +
          5 * (9 * ENNReal.ofReal CW * wtP p (1 / (2 : ℝ) ^ r) f +
            ENNReal.ofReal (1 / (2 * 2 ^ (e r))))) :
    lqNorm q (stratSeq p s (Pendencias.Agenda.Sigma H) f) ≤
      (2 * (2 : ℝ≥0∞) ^ (q.toReal)⁻¹) *
        ((1 + 5 * (9 * ENNReal.ofReal CW)) * ENNReal.ofReal B +
          5 * lqNorm q (quantWeight s e)) := by
  let w := quantWeight s e
  have hpt : ∀ k : ℕ, stratSeq p s (Pendencias.Agenda.Sigma H) f k ≤
      (1 + 5 * (9 * ENNReal.ofReal CW)) * besovSeq p s f (k + 1) + 5 * w k := by
    intro k
    have hR := hscale (k + 1) (Nat.le_add_left 1 k)
    calc stratSeq p s (Pendencias.Agenda.Sigma H) f k
        = ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            realP p (Pendencias.Agenda.Sigma H) (2 ^ (k + 1)) f := rfl
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
            (wtP p (1 / (2 : ℝ) ^ (k + 1)) f +
              5 * (9 * ENNReal.ofReal CW * wtP p (1 / (2 : ℝ) ^ (k + 1)) f +
                ENNReal.ofReal (1 / (2 * 2 ^ (e (k + 1)))))) := mul_le_mul_right hR _
      _ = (1 + 5 * (9 * ENNReal.ofReal CW)) * besovSeq p s f (k + 1) + 5 * w k := by
          simp only [besovSeq, w, quantWeight]
          ring
  have hball' : lqNorm q (besovSeq p s f) ≤ ENNReal.ofReal B :=
    (lqNorm_le_besovNorm p s q f).trans hball
  have hshift : lqNorm q (fun k : ℕ => besovSeq p s f (k + 1)) ≤ ENNReal.ofReal B :=
    (lq_shift_le hq (besovSeq p s f)).trans hball'
  calc lqNorm q (stratSeq p s (Pendencias.Agenda.Sigma H) f)
      ≤ lqNorm q (fun k => (1 + 5 * (9 * ENNReal.ofReal CW)) * besovSeq p s f (k + 1) +
          5 * w k) := lq_mono hq hpt
    _ ≤ (2 * (2 : ℝ≥0∞) ^ (q.toReal)⁻¹) *
          (lqNorm q (fun k => (1 + 5 * (9 * ENNReal.ofReal CW)) * besovSeq p s f (k + 1)) +
            lqNorm q (fun k => 5 * w k)) := lq_add_le hq _ _
    _ ≤ (2 * (2 : ℝ≥0∞) ^ (q.toReal)⁻¹) *
          ((1 + 5 * (9 * ENNReal.ofReal CW)) * ENNReal.ofReal B + 5 * lqNorm q w) := by
        gcongr
        · exact (lq_const_mul_le hq _ _).trans (mul_le_mul_right hshift _)
        · exact lq_const_mul_le hq _ _

/-- **Taxa uniforme em `ℓ^q`.** Se a sequência de quantização tem norma `ℓ^q` finita `W`, então
`‖(2^{rs} R_{2^r}(f))‖_{ℓ^q} ≤ K_q (c₁ B + 5 W)`. -/
theorem unif_rate {p : ℝ} (hp : 1 ≤ p) {s : ℝ} {q : ℝ≥0∞} (hq : 0 < q) :
    ∃ CW Cs : ℝ, 0 ≤ CW ∧ 1 ≤ Cs ∧ ∀ B : ℝ, 1 ≤ B → ∀ (e H : ℕ → ℕ),
      (∀ r, 1 ≤ r → r ≤ e r) →
      (∀ r, 1 ≤ r → 8 * (Cs * B * LamU p s q r + 1) * 2 ^ (e r) ≤ (H (2 ^ r) : ℝ)) →
      ∀ f : ℝ → ℝ, Measurable f → besovNorm (ENNReal.ofReal p) s q f ≤ ENNReal.ofReal B →
        lqNorm q (stratSeq (ENNReal.ofReal p) s (Pendencias.Agenda.Sigma H) f) ≤
          (2 * (2 : ℝ≥0∞) ^ (q.toReal)⁻¹) *
            ((1 + 5 * (9 * ENNReal.ofReal CW)) * ENNReal.ofReal B +
              5 * lqNorm q (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * s)) *
                ENNReal.ofReal (1 / (2 * 2 ^ (e (k + 1)))))) := by
  obtain ⟨CW, Cs, hCW, hCs1, hcore⟩ := unif_core (p := p) (s := s) hp hq
  refine ⟨CW, Cs, hCW, hCs1, fun B hB e H hre hH f hf hball => ?_⟩
  exact unif_rate_of_scale hq hball fun r hr ↦
    (hcore B hB e H hre hH f hf hball r hr).choose_spec.2.2

end FormalizacaoLow
