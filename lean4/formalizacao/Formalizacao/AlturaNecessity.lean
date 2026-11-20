import Formalizacao.AlturaSlope

/-!
# Necessidade da altura (auditoria, Partes II e IV)

Consequências dos pisos geométrico, de inclinação e aritmético para a altura de qualquer agenda
que atinja uma taxa uniforme `C N^{-σ}` sobre a bola unitária de Besov:

* `geometric_necessity`: `H(N) ≥ (c/C)^{1/s} N` para todo `0 < s < 2`;
* `slope_necessity`: `H(N) ≥ (c/C)^{1/β} N^{s/β}` com `β = s/(1+1/p-s)` para `s ≤ 1/p`
  (expoente `s/β = 1 + 1/p - s`);
* `arithmetic_necessity`: `H(N) ≥ N^s/(2C)` (piso aritmético, com a constante `f ≡ 1/(2H)`).

As constantes `c` dependem apenas de `(p,s,q)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoAltura

open FormalizacaoLp FormalizacaoLow FormalizacaoRed

/-! ## Álgebra das taxas -/

/-- Se `c h^{-γ} ≤ C N^{-σ}` então `(c/C)^{1/γ} N^{σ/γ} ≤ h`. -/
lemma height_of_rate {c C γ σ N h : ℝ} (hc : 0 < c) (hC : 0 < C) (hγ : 0 < γ) (hN : 0 < N)
    (hh : 0 < h) (hbd : c * h ^ (-γ) ≤ C * N ^ (-σ)) :
    (c / C) ^ γ⁻¹ * N ^ (σ / γ) ≤ h := by
  -- `c h^{-γ} ≤ C N^{-σ}` ⇔ `c N^σ ≤ C h^γ`
  have h1 : c * N ^ σ ≤ C * h ^ γ := by
    have hhγ : 0 < h ^ γ := Real.rpow_pos_of_pos hh γ
    have hNσ : 0 < N ^ σ := Real.rpow_pos_of_pos hN σ
    rw [Real.rpow_neg hh.le, Real.rpow_neg hN.le] at hbd
    have key := mul_le_mul_of_nonneg_right hbd (mul_pos hhγ hNσ).le
    have e1 : c * (h ^ γ)⁻¹ * (h ^ γ * N ^ σ) = c * N ^ σ := by field_simp
    have e2 : C * (N ^ σ)⁻¹ * (h ^ γ * N ^ σ) = C * h ^ γ := by field_simp
    linarith
  -- `(c/C) N^σ ≤ h^γ`
  have h3 : (c / C) * N ^ σ ≤ h ^ γ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    linarith [h1, mul_comm C (h ^ γ)]
  -- tomar a potência `1/γ`
  have h4 : ((c / C) * N ^ σ) ^ γ⁻¹ ≤ (h ^ γ) ^ γ⁻¹ :=
    Real.rpow_le_rpow (by positivity) h3 (inv_nonneg.mpr hγ.le)
  rw [← Real.rpow_mul hh.le, mul_inv_cancel₀ hγ.ne', Real.rpow_one] at h4
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN.le] at h4
  exact h4

/-! ## Constantes na bola de Besov -/

/-- Funções constantes `c ∈ [0,1]` têm norma de Besov `≤ 1` (segundas diferenças nulas). -/
lemma besovNorm_const_le {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hq0 : 0 < q)
    (hs : 0 < s) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    besovNorm p s q (fun _ => c) ≤ 1 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hwt : ∀ τ : ℝ, wtP p τ (fun _ => c) = 0 := by
    intro τ
    unfold wtP
    apply le_antisymm _ (zero_le _)
    refine iSup₂_le fun h _ => ?_
    have : diff2 h (fun _ => c) = fun _ => 0 := by
      funext x; simp [diff2]; ring
    rw [this]; simp
  have hseq : besovSeq p s (fun _ => c) = fun _ => 0 := by
    funext r; unfold besovSeq; rw [hwt]; simp
  have hlq : lqNorm q (besovSeq p s (fun _ => c)) = 0 := by
    rw [hseq]
    unfold lqNorm
    split_ifs with hqt
    · simp
    · have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0.ne' hqt
      simp only [ENNReal.zero_rpow_of_pos hQ, tsum_zero, ENNReal.zero_rpow_of_pos (inv_pos.mpr hQ)]
  have hE : eLpNorm (fun _ => c) p (volume.restrict (Icc (0 : ℝ) 1)) = ENNReal.ofReal c := by
    rw [eLpNorm_const' c hp0 hpt]
    simp [Real.volume_Icc, Real.enorm_eq_ofReal hc0]
  unfold besovNorm
  rw [hE, hlq, add_zero]
  exact ENNReal.ofReal_le_one.mpr hc1

/-! ## Necessidade -/

/-- **Necessidade geométrica.** Se `sup_f e^h_{N,p}(f) ≤ C N^{-s}` sobre a bola unitária, então
`(c/C)^{1/s} N ≤ h` para toda agenda constante `h ≥ 2`. -/
theorem geometric_necessity {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hq0 : 0 < q)
    (hs : 0 < s) (hs2 : s < 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C : ℝ) (N h : ℕ), 0 < C → 1 ≤ N → 2 ≤ h →
      (∀ f : ℝ → ℝ, Measurable f → besovNorm p s q f ≤ 1 →
        FormalizacaoFloor.bestError p N h f ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-s))) →
      (c / C) ^ s⁻¹ * (N : ℝ) ≤ (h : ℝ) := by
  obtain ⟨c, hc, hfl⟩ := geometric_floor hp1 hpt hq0 hs hs2
  refine ⟨c, hc, fun C N h hC hN hh hrate => ?_⟩
  obtain ⟨f, hfm, hball, hdist⟩ := hfl h hh
  have hlow : ENNReal.ofReal (c * (h : ℝ) ^ (-s)) ≤ FormalizacaoFloor.bestError p N h f :=
    le_iInf₂ fun g hg => hdist N g hg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hbd : c * (h : ℝ) ^ (-s) ≤ C * (N : ℝ) ^ (-s) := by
    have hup := hlow.trans (hrate f hfm hball)
    rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le
      (Real.rpow_nonneg hNpos.le _))] at hup
    exact hup
  have := height_of_rate hc hC hs hNpos hhpos hbd
  rwa [div_self hs.ne', Real.rpow_one] at this

/-- **Necessidade no regime de inclinação** (`s ≤ 1/p`): `H(N) ≥ (c/C)^{1/β} N^{1+1/p-s}`,
com `β = s/(1 + 1/p - s)`. -/
theorem slope_necessity {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hq0 : 0 < q)
    (hs : 0 < s) (hs2 : s < 2) (hsp : s ≤ p.toReal⁻¹) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C : ℝ) (N h : ℕ), 0 < C → 1 ≤ N → 2 ≤ h →
      (∀ f : ℝ → ℝ, Measurable f → besovNorm p s q f ≤ 1 →
        FormalizacaoFloor.bestError p N h f ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-s))) →
      (c / C) ^ (s / (1 + (p.toReal⁻¹ - s)))⁻¹ * (N : ℝ) ^ (1 + (p.toReal⁻¹ - s)) ≤ (h : ℝ) := by
  obtain ⟨c, hc, hfl⟩ := slope_floor hp1 hpt hq0 hs hs2 hsp
  refine ⟨c, hc, fun C N h hC hN hh hrate => ?_⟩
  obtain ⟨f, hfm, hball, hdist⟩ := hfl h hh
  set β : ℝ := s / (1 + (p.toReal⁻¹ - s)) with hβ
  have hβpos : 0 < β := by
    rw [hβ]; apply div_pos hs; have := hsp; linarith
  have hlow : ENNReal.ofReal (c * (h : ℝ) ^ (-β)) ≤ FormalizacaoFloor.bestError p N h f :=
    le_iInf₂ fun g hg => hdist N g hg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hbd : c * (h : ℝ) ^ (-β) ≤ C * (N : ℝ) ^ (-s) := by
    have hup := hlow.trans (hrate f hfm hball)
    rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (Real.rpow_nonneg hNpos.le _))] at hup
    exact hup
  have := height_of_rate hc hC hβpos hNpos hhpos hbd
  have e : s / β = 1 + (p.toReal⁻¹ - s) := by
    rw [hβ]; field_simp
  rw [e] at this
  exact this

/-- **Piso aritmético.** Para `h ≥ 1`, `f ≡ 1/(2h)` tem norma de Besov `≤ 1` e
`H(N) ≥ N^s/(2C)`: `(1/(2C)) N^s ≤ h`. -/
theorem arithmetic_necessity {p q : ℝ≥0∞} {s : ℝ} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (hq0 : 0 < q)
    (hs : 0 < s) {C : ℝ} (hC : 0 < C) {N h : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h)
    (hrate : ∀ f : ℝ → ℝ, Measurable f → besovNorm p s q f ≤ 1 →
      FormalizacaoFloor.bestError p N h f ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-s))) :
    (1 / (2 * C)) * (N : ℝ) ^ s ≤ (h : ℝ) := by
  have hval : (1 : ℝ) / (2 * (h : ℝ)) ≤ 1 := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    rw [div_le_one (by positivity)]; linarith
  have hball := besovNorm_const_le hp1 hpt hq0 hs (c := FormalizacaoFloor.floorValue h)
    (by unfold FormalizacaoFloor.floorValue; positivity)
    (by unfold FormalizacaoFloor.floorValue; exact hval)
  have hlow := FormalizacaoFloor.arithmetic_floor_bestError hp1 N hh
    (H := h)
  have hup := hlow.trans (hrate _ measurable_const hball)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hbd : (1 / 2 : ℝ) * (h : ℝ) ^ (-(1 : ℝ)) ≤ C * (N : ℝ) ^ (-s) := by
    rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (Real.rpow_nonneg hNpos.le _))] at hup
    unfold FormalizacaoFloor.floorValue at hup
    rw [Real.rpow_neg_one]
    have : (1 : ℝ) / (2 * (h : ℝ)) = 1 / 2 * (h : ℝ)⁻¹ := by ring
    rw [this] at hup
    exact hup
  have := height_of_rate (by norm_num) hC one_pos hNpos hhpos hbd
  rw [inv_one, div_one, Real.rpow_one, div_div] at this
  exact this

end FormalizacaoAltura
