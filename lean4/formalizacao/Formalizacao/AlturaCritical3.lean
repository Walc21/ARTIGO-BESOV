import Formalizacao.AlturaCritical2
import Formalizacao.AlturaLq

/-!
# Altura linear crítica: a cota em `ℓ^q` (auditoria, Parte V)

Com a agenda `H_B(N) = ⌈A (B+1)(N+1)⌉`, a sequência `(2^{rs} R_{2^r}^{H_B}(f))_{r≥1}` tem norma
`ℓ^q` limitada por `C(B+1)`, com `C` dependendo só de `(p, q, C_W)`, quando `‖f‖_B ≤ B`. Para
`p > 1`, `s = 1/p < 1`, e `q < ∞`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoCrit3

open FormalizacaoCrit FormalizacaoCrit2 FormalizacaoLp FormalizacaoLow FormalizacaoRed
open FormalizacaoFloor Artigo FormalizacaoLq FormalizacaoLqAux FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

/-- Constante `C₀` com `B₀ ≤ C₀ B`. -/
noncomputable def C0c (p CW : ℝ) : ℝ := 8 * (2 : ℝ) ^ (1 / p) * (1 + 9 * CW)

/-- Constante `C_M` com `M_ℓ + 1 ≤ C_M (B+1)(ℓ+1)`. -/
noncomputable def CMc (p CW : ℝ) : ℝ := C0c p CW + 144 * CW * (2 : ℝ) ^ (1 / p) + 1

/-- Constante `C_J` com `J + 1 ≤ C_J (B+1)`. -/
noncomputable def CJc (p CW : ℝ) : ℝ := 4 * C0c p CW + 288 * CW * (2 : ℝ) ^ (1 / p) + 1

/-- Constante da agenda `A`. -/
noncomputable def Avc (p CW : ℝ) : ℝ := 16 * CMc p CW + CJc p CW + 8

/-- Agenda crítica `H_B(N) = ⌈A (B+1)(N+1)⌉`. -/
noncomputable def criticalAgenda (p CW B : ℝ) : ℕ → ℕ :=
  fun N => ⌈Avc p CW * (B + 1) * ((N : ℝ) + 1)⌉₊

/-- Condições de altura do nível `ℓ ≥ 1` (com `B₀ ≤ C₀ B`). -/
lemma level_conditions {p CW B : ℝ} (hp : 1 < p) (hCW : 0 ≤ CW) (hB : 0 ≤ B) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) {B0 : ℝ} (hB0 : B0 ≤ C0c p CW * B) :
    8 * (2 : ℝ) ^ ℓ ≤ (criticalAgenda p CW B (2 ^ ℓ) : ℝ) ∧
    16 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ + 1) ≤ (criticalAgenda p CW B (2 ^ ℓ) : ℝ) ∧
    (2 : ℝ) ^ ℓ * (4 * B0 + 288 * CW * (2 : ℝ) ^ (1 / p) * B + 1) ≤
      (criticalAgenda p CW B (2 ^ ℓ) : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hc1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / p) := Real.one_le_rpow (by norm_num) (by positivity)
  have hC0 : 0 ≤ C0c p CW := by unfold C0c; positivity
  have hCM0 : 0 ≤ CMc p CW := by unfold CMc; positivity
  have hCJ0 : 0 ≤ CJc p CW := by unfold CJc; positivity
  have hAv16 : 16 * CMc p CW ≤ Avc p CW := by unfold Avc; linarith
  have hAvJ : CJc p CW ≤ Avc p CW := by unfold Avc; linarith
  have hAv8 : 8 ≤ Avc p CW := by unfold Avc; linarith
  have hcast : (((2 ^ ℓ : ℕ)) : ℝ) = (2 : ℝ) ^ ℓ := by push_cast; ring
  set Y : ℝ := ((2 ^ ℓ : ℕ) : ℝ) + 1 with hY
  have hY2 : (2 : ℝ) ^ ℓ ≤ Y := by rw [hY, hcast]; linarith
  have hYl : (ℓ : ℝ) + 1 ≤ Y := by
    have h1 : (ℓ : ℝ) < (2 : ℝ) ^ ℓ := by
      have := Nat.lt_two_pow_self (n := ℓ)
      exact_mod_cast this
    rw [hY, hcast]; linarith
  have hX : Avc p CW * (B + 1) * Y ≤ (criticalAgenda p CW B (2 ^ ℓ) : ℝ) := by
    unfold criticalAgenda
    have := Nat.le_ceil (Avc p CW * (B + 1) * (((2 ^ ℓ : ℕ) : ℝ) + 1))
    rw [hY]; exact this
  have hB1 : (1 : ℝ) ≤ B + 1 := by linarith
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- 8·2^ℓ ≤ A (B+1) Y
    have h1 : 8 * (2 : ℝ) ^ ℓ ≤ Avc p CW * (2 : ℝ) ^ ℓ := by
      exact mul_le_mul_of_nonneg_right hAv8 h2pos.le
    have h2 : Avc p CW * (2 : ℝ) ^ ℓ ≤ Avc p CW * (B + 1) * Y := by
      have hA0 : 0 ≤ Avc p CW := by linarith
      calc Avc p CW * (2 : ℝ) ^ ℓ ≤ Avc p CW * (B + 1) * (2 : ℝ) ^ ℓ := by
            apply mul_le_mul_of_nonneg_right _ h2pos.le
            nlinarith
        _ ≤ Avc p CW * (B + 1) * Y := by
            apply mul_le_mul_of_nonneg_left hY2 (by positivity)
    linarith
  · -- 16 (B₀ + 144 c B ℓ + 1) ≤ 16 C_M (B+1)(ℓ+1) ≤ A(B+1)Y
    have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    have hB0' : 16 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ + 1) ≤
        16 * (C0c p CW * B + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ + 1) := by
      have : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ := by positivity
      linarith
    have hCMexp : C0c p CW * B + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ + 1 ≤
        CMc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) := by
      unfold CMc
      nlinarith [mul_nonneg hC0 hB, mul_nonneg hC0 hℓ0, mul_nonneg (mul_nonneg hCW (by positivity : (0:ℝ) ≤ (2:ℝ)^(1/p))) hB,
        mul_nonneg hC0 (mul_nonneg hB hℓ0), mul_nonneg (by positivity : (0:ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p)) hB,
        mul_nonneg (by positivity : (0:ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p)) (mul_nonneg hB hℓ0),
        mul_nonneg (by positivity : (0:ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p)) hℓ0,
        mul_nonneg hC0 hℓ0, mul_nonneg hB hℓ0]
    have hstep : 16 * CMc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) ≤ Avc p CW * (B + 1) * Y := by
      have h1 : 16 * CMc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) ≤ Avc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hAv16 (by positivity)
      have h2 : Avc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) ≤ Avc p CW * (B + 1) * Y := by
        have : (B + 1) * ((ℓ : ℝ) + 1) ≤ (B + 1) * Y :=
          mul_le_mul_of_nonneg_left hYl (by linarith)
        calc Avc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) ≤ Avc p CW * ((B + 1) * Y) :=
              mul_le_mul_of_nonneg_left this (by unfold Avc; linarith)
          _ = Avc p CW * (B + 1) * Y := by ring
      linarith
    have := mul_le_mul_of_nonneg_left hCMexp (by norm_num : (0 : ℝ) ≤ 16)
    have hfinal : 16 * (C0c p CW * B + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ + 1) ≤
        Avc p CW * (B + 1) * Y := by
      nlinarith [this, hstep]
    linarith [hfinal, hX]
  · -- 2^ℓ (4B₀ + 288 c B + 1) ≤ 2^ℓ C_J (B+1) ≤ A(B+1)Y
    have hJ0 : 4 * B0 + 288 * CW * (2 : ℝ) ^ (1 / p) * B + 1 ≤
        CJc p CW * (B + 1) := by
      unfold CJc
      have : 4 * B0 ≤ 4 * (C0c p CW * B) := by linarith
      nlinarith [mul_nonneg hC0 hB, mul_nonneg (by positivity : (0:ℝ) ≤ 288 * CW * (2:ℝ)^(1/p)) hB]
    have h1 : (2 : ℝ) ^ ℓ * (4 * B0 + 288 * CW * (2 : ℝ) ^ (1 / p) * B + 1) ≤
        (2 : ℝ) ^ ℓ * (CJc p CW * (B + 1)) := mul_le_mul_of_nonneg_left hJ0 h2pos.le
    have h2 : (2 : ℝ) ^ ℓ * (CJc p CW * (B + 1)) ≤ Avc p CW * (B + 1) * Y := by
      have hA : CJc p CW * (B + 1) ≤ Avc p CW * (B + 1) := mul_le_mul_of_nonneg_right hAvJ (by linarith)
      calc (2 : ℝ) ^ ℓ * (CJc p CW * (B + 1)) ≤ Y * (Avc p CW * (B + 1)) :=
            mul_le_mul hY2 (by linarith) (by positivity) (by positivity)
        _ = Avc p CW * (B + 1) * Y := by ring
    linarith [hX, h1, h2]

end FormalizacaoCrit3

namespace FormalizacaoCrit3

open FormalizacaoCrit FormalizacaoCrit2 FormalizacaoLp FormalizacaoLow FormalizacaoRed
open FormalizacaoFloor Artigo FormalizacaoLq FormalizacaoLqAux FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

/-- `M_ℓ + 1 ≤ C_M (B+1)(ℓ+1)` (com `B₀ ≤ C₀ B`). -/
lemma M_le {p CW B : ℝ} (hp : 1 < p) (hCW : 0 ≤ CW) (hB : 0 ≤ B) {ℓ : ℕ} {B0 : ℝ}
    (hB0 : B0 ≤ C0c p CW * B) :
    B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ + 1 ≤ CMc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) := by
  have hp0 : 0 < p := by linarith
  have hC0 : 0 ≤ C0c p CW := by unfold C0c; positivity
  have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  have hc0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / p) := by positivity
  have key : C0c p CW * B + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ + 1 ≤
      CMc p CW * ((B + 1) * ((ℓ : ℝ) + 1)) := by
    unfold CMc
    have e : (C0c p CW + 144 * CW * (2 : ℝ) ^ (1 / p) + 1) * ((B + 1) * ((ℓ : ℝ) + 1)) =
        C0c p CW * (B + 1) * ((ℓ : ℝ) + 1) + 144 * CW * (2 : ℝ) ^ (1 / p) * (B + 1) * ((ℓ : ℝ) + 1)
          + (B + 1) * ((ℓ : ℝ) + 1) := by ring
    rw [e]
    have h1 : C0c p CW * B ≤ C0c p CW * (B + 1) * ((ℓ : ℝ) + 1) := by
      have : 0 ≤ C0c p CW * (B + 1) * ℓ := by positivity
      nlinarith
    have h2 : 144 * CW * (2 : ℝ) ^ (1 / p) * B * ℓ ≤
        144 * CW * (2 : ℝ) ^ (1 / p) * (B + 1) * ((ℓ : ℝ) + 1) := by
      have hk : (0 : ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p) := by positivity
      have : B * ℓ ≤ (B + 1) * ((ℓ : ℝ) + 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hk]
    have h3 : (1 : ℝ) ≤ (B + 1) * ((ℓ : ℝ) + 1) := by nlinarith
    linarith
  linarith [key, hB0]

end FormalizacaoCrit3

namespace FormalizacaoCrit3

open FormalizacaoCrit FormalizacaoCrit2 FormalizacaoLp FormalizacaoLow FormalizacaoRed
open FormalizacaoFloor Artigo FormalizacaoLq FormalizacaoLqAux FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

/-- Majorante do erro de quantização: `2^{(r+1)/p}·8(M+1)/H ≤ (8 C_M ρ/A)(r+2)ρ^r`,
com `ρ = 2^{1/p - 1}`. -/
lemma E_majorant {p CW B : ℝ} (hp : 1 < p) (hCW : 0 ≤ CW) (hB : 0 ≤ B) (r : ℕ) {B0 : ℝ}
    (hB0 : B0 ≤ C0c p CW * B) {H : ℕ}
    (hH : Avc p CW * (B + 1) * (((2 ^ (r + 1) : ℕ) : ℝ) + 1) ≤ (H : ℝ)) :
    (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p)) *
        (8 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) / (H : ℝ)) ≤
      (8 * CMc p CW * (2 : ℝ) ^ (1 / p - 1) / Avc p CW) * (((r : ℝ) + 2) * ((2 : ℝ) ^ (1 / p - 1)) ^ r) := by
  have hp0 : 0 < p := by linarith
  set ρ : ℝ := (2 : ℝ) ^ (1 / p - 1) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hc0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / p) := by positivity
  have hC0 : 0 ≤ C0c p CW := by
    unfold C0c
    have h19 : (0 : ℝ) ≤ 1 + 9 * CW := by linarith
    have h8 : (0 : ℝ) ≤ 8 * (2 : ℝ) ^ (1 / p) := by positivity
    exact mul_nonneg h8 h19
  have hCM : 0 ≤ CMc p CW := by
    unfold CMc
    have : (0:ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p) := by
      have := mul_nonneg hCW hc0; linarith
    linarith
  have hCJ : 0 ≤ CJc p CW := by
    unfold CJc
    have : (0:ℝ) ≤ 288 * CW * (2 : ℝ) ^ (1 / p) := by
      have := mul_nonneg hCW hc0; linarith
    linarith
  have hA : 0 < Avc p CW := by
    unfold Avc; linarith
  have hM := M_le hp hCW hB (ℓ := r + 1) hB0
  have hM' : B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1 ≤
      CMc p CW * ((B + 1) * ((r : ℝ) + 2)) := by
    have : ((r + 1 : ℕ) : ℝ) + 1 = (r : ℝ) + 2 := by push_cast; ring
    rw [← this]; exact hM
  have hBp : 0 < B + 1 := by linarith
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    have : 0 < Avc p CW * (B + 1) * (((2 ^ (r + 1) : ℕ) : ℝ) + 1) := by positivity
    linarith
  -- 2^{r+1} ≤ 2^{r+1} + 1
  have h2r : (2 : ℝ) ^ (r + 1) ≤ ((2 ^ (r + 1) : ℕ) : ℝ) + 1 := by
    push_cast; linarith
  have hHlow : Avc p CW * (B + 1) * (2 : ℝ) ^ (r + 1) ≤ (H : ℝ) := by
    have : Avc p CW * (B + 1) * (2 : ℝ) ^ (r + 1) ≤ Avc p CW * (B + 1) * (((2 ^ (r + 1) : ℕ) : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      push_cast at h2r ⊢; linarith
    linarith
  -- 2^{r+1}·8(M+1)/H ≤ 8 C_M (r+2)/A
  have hE : (2 : ℝ) ^ (r + 1) * (8 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) / (H : ℝ))
      ≤ 8 * CMc p CW * ((r : ℝ) + 2) / Avc p CW := by
    have hnum : 8 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) ≤
        8 * (CMc p CW * ((B + 1) * ((r : ℝ) + 2))) := by linarith
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (r + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hHpos hA]
    calc (2 : ℝ) ^ (r + 1) * (8 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1)) * Avc p CW
        ≤ (2 : ℝ) ^ (r + 1) * (8 * (CMc p CW * ((B + 1) * ((r : ℝ) + 2)))) * Avc p CW := by
          apply mul_le_mul_of_nonneg_right _ hA.le
          exact mul_le_mul_of_nonneg_left hnum h2pos.le
      _ = (8 * CMc p CW * ((r : ℝ) + 2)) * (Avc p CW * (B + 1) * (2 : ℝ) ^ (r + 1)) := by ring
      _ ≤ (8 * CMc p CW * ((r : ℝ) + 2)) * (H : ℝ) := by
          apply mul_le_mul_of_nonneg_left hHlow
          have : (0 : ℝ) ≤ CMc p CW := hCM
          positivity
      _ = 8 * CMc p CW * ((r : ℝ) + 2) * (H : ℝ) := rfl
  -- fator `2^{(r+1)/p} = ρ^{r+1} 2^{r+1}`
  have hfac : (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p)) = ρ ^ (r + 1) * (2 : ℝ) ^ (r + 1) := by
    have e : ρ ^ (r + 1) * (2 : ℝ) ^ (r + 1) = (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p)) := by
      rw [hρ, ← Real.rpow_natCast ((2 : ℝ) ^ (1 / p - 1)) (r + 1), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast (2 : ℝ) (r + 1), ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    exact e.symm
  rw [hfac]
  have hρr : ρ ^ (r + 1) = ρ * ρ ^ r := by ring
  calc ρ ^ (r + 1) * (2 : ℝ) ^ (r + 1) * (8 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) / (H : ℝ))
      = ρ ^ (r + 1) * ((2 : ℝ) ^ (r + 1) * (8 * (B0 + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) / (H : ℝ))) := by ring
    _ ≤ ρ ^ (r + 1) * (8 * CMc p CW * ((r : ℝ) + 2) / Avc p CW) := by
        apply mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (8 * CMc p CW * ρ / Avc p CW) * (((r : ℝ) + 2) * ρ ^ r) := by
        rw [hρr]; ring
    _ = (8 * CMc p CW * (2 : ℝ) ^ (1 / p - 1) / Avc p CW) * (((r : ℝ) + 2) * ((2 : ℝ) ^ (1 / p - 1)) ^ r) := by
        rw [hρ]

end FormalizacaoCrit3

namespace FormalizacaoCrit3

open FormalizacaoCrit FormalizacaoCrit2 FormalizacaoLp FormalizacaoLow FormalizacaoRed
open FormalizacaoFloor Artigo FormalizacaoLq FormalizacaoLqAux FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

/-- Cota real final: `(z₁^Q + z₂^Q)^{1/Q} ≤ (K₁^Q + K₂^Q)^{1/Q}(B+1)` com `z₁ ≤ K₁ B`, `z₂ ≤ K₂`. -/
lemma final_real {Q K₁ K₂ B : ℝ} (hQ : 0 < Q) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hB : 0 ≤ B) :
    ((K₁ * B) ^ Q + K₂ ^ Q) ^ Q⁻¹ ≤ (K₁ ^ Q + K₂ ^ Q) ^ Q⁻¹ * (B + 1) := by
  have h1 : (K₁ * B) ^ Q + K₂ ^ Q ≤ (K₁ ^ Q + K₂ ^ Q) * (B + 1) ^ Q := by
    have hBQ : B ^ Q ≤ (B + 1) ^ Q := Real.rpow_le_rpow hB (by linarith) hQ.le
    have hB1Q : (1 : ℝ) ≤ (B + 1) ^ Q := Real.one_le_rpow (by linarith) hQ.le
    rw [Real.mul_rpow hK₁ hB]
    have hK1Q : 0 ≤ K₁ ^ Q := Real.rpow_nonneg hK₁ _
    have hK2Q : 0 ≤ K₂ ^ Q := Real.rpow_nonneg hK₂ _
    nlinarith [mul_le_mul_of_nonneg_left hBQ hK1Q, mul_le_mul_of_nonneg_left hB1Q hK2Q]
  calc ((K₁ * B) ^ Q + K₂ ^ Q) ^ Q⁻¹ ≤ ((K₁ ^ Q + K₂ ^ Q) * (B + 1) ^ Q) ^ Q⁻¹ :=
        Real.rpow_le_rpow (by positivity) h1 (inv_nonneg.mpr hQ.le)
    _ = (K₁ ^ Q + K₂ ^ Q) ^ Q⁻¹ * ((B + 1) ^ Q) ^ Q⁻¹ := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = (K₁ ^ Q + K₂ ^ Q) ^ Q⁻¹ * (B + 1) := by
        rw [← Real.rpow_mul (by linarith), mul_inv_cancel₀ hQ.ne', Real.rpow_one]

end FormalizacaoCrit3

namespace FormalizacaoCrit3

open FormalizacaoCrit FormalizacaoCrit2 FormalizacaoLp FormalizacaoLow FormalizacaoRed
open FormalizacaoFloor Artigo FormalizacaoLq FormalizacaoLqAux FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

lemma CM_nonneg {p CW : ℝ} (hp : 1 < p) (hCW : 0 ≤ CW) : 0 ≤ CMc p CW := by
  have hc0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / p) := by positivity
  have hC0 : 0 ≤ C0c p CW := by
    unfold C0c
    have h19 : (0 : ℝ) ≤ 1 + 9 * CW := by linarith
    have h8 : (0 : ℝ) ≤ 8 * (2 : ℝ) ^ (1 / p) := by positivity
    exact mul_nonneg h8 h19
  have : (0 : ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p) := by
    have := mul_nonneg hCW hc0; linarith
  unfold CMc; linarith

lemma Avc_pos {p CW : ℝ} (hp : 1 < p) (hCW : 0 ≤ CW) : 0 < Avc p CW := by
  have hCM := CM_nonneg hp hCW
  have hc0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / p) := by positivity
  have hC0 : 0 ≤ C0c p CW := by
    unfold C0c
    have h19 : (0 : ℝ) ≤ 1 + 9 * CW := by linarith
    have h8 : (0 : ℝ) ≤ 8 * (2 : ℝ) ^ (1 / p) := by positivity
    exact mul_nonneg h8 h19
  have hCJ : 0 ≤ CJc p CW := by
    unfold CJc
    have : (0 : ℝ) ≤ 288 * CW * (2 : ℝ) ^ (1 / p) := by
      have := mul_nonneg hCW hc0; linarith
    linarith
  unfold Avc; linarith

end FormalizacaoCrit3

namespace FormalizacaoCrit3

open FormalizacaoCrit FormalizacaoCrit2 FormalizacaoLp FormalizacaoLow FormalizacaoRed
open FormalizacaoFloor Artigo FormalizacaoLq FormalizacaoLqAux FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

/-- **Cota `ℓ^q` da altura crítica.** Para `1 < p`, `s = 1/p`, `0 < q < ∞`, a sequência
`(2^{rs} R_{2^{r+1}}^{H_B}(f))_{r≥0}` tem norma `ℓ^q` `≤ C_q (B+1)` quando `‖f‖_B ≤ B`. -/
theorem critical_lq {p CW : ℝ} {q : ℝ≥0∞} (hp : 1 < p) (hW : FormalizacaoCor.WhitneyLp p CW)
    (hCW : 0 ≤ CW) (hq0 : 0 < q) (hqt : q ≠ ⊤) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (f : ℝ → ℝ) (B : ℝ), Measurable f → 1 ≤ B →
      besovNorm (ENNReal.ofReal p) (1 / p) q f ≤ ENNReal.ofReal B →
      lqNorm q (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p))) *
        realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
          (2 ^ (r + 1)) f) ≤ ENNReal.ofReal (Cq * (B + 1)) := by
  have hp0 : 0 < p := by linarith
  have hQ0 : 0 < q.toReal := ENNReal.toReal_pos hq0.ne' hqt
  set ρ : ℝ := (2 : ℝ) ^ (1 / p - 1) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  set σ : ℝ := (1 + ρ) / 2 with hσ
  have hρσ : ρ < σ := by rw [hσ]; linarith
  have hσ1 : σ < 1 := by rw [hσ]; linarith
  have hσ0 : 0 ≤ σ := by rw [hσ]; linarith
  obtain ⟨K', hK'0, hK'⟩ := poly_geom_majorant hρ0 hρσ
  have hCM := CM_nonneg hp hCW
  have hA := Avc_pos hp hCW
  set Kmaj : ℝ := 8 * CMc p CW * ρ / Avc p CW with hKmaj
  have hKmaj0 : 0 ≤ Kmaj := by rw [hKmaj]; positivity
  set Cw : ℝ := 5 * Kmaj * K' with hCw
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  set wseq : ℕ → ℝ≥0∞ := fun r => ENNReal.ofReal (Cw * σ ^ r) with hwseq
  have hwfin : lqNorm q wseq < ⊤ :=
    lq_of_geom_le hq0 hqt hCw0 hσ0 hσ1 (fun k => le_rfl)
  set Dw : ℝ := (lqNorm q wseq).toReal with hDw_def
  have hDw : lqNorm q wseq = ENNReal.ofReal Dw := (ENNReal.ofReal_toReal hwfin.ne).symm
  have hDw0 : 0 ≤ Dw := ENNReal.toReal_nonneg
  set Q : ℝ := q.toReal with hQ
  have h1CW : 0 ≤ 1 + 45 * CW := by linarith
  have hCq0 : 0 ≤ 2 * ((1 + 45 * CW) ^ Q + Dw ^ Q) ^ Q⁻¹ := by
    apply mul_nonneg (by norm_num)
    apply Real.rpow_nonneg
    have := Real.rpow_nonneg h1CW Q
    have := Real.rpow_nonneg hDw0 Q
    linarith
  refine ⟨2 * ((1 + 45 * CW) ^ Q + Dw ^ Q) ^ Q⁻¹, hCq0, fun f B hf hB1 hbes => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  -- consequências da norma de Besov
  have hfin : Np p f (Icc 0 1) < ⊤ :=
    lt_of_le_of_lt ((eLpNorm_le_besovNorm (ENNReal.ofReal p) (1 / p) q f).trans hbes)
      ENNReal.ofReal_lt_top
  have hfi : IntegrableOn f (Icc 0 1) := by
    have hmem : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨hf.aestronglyMeasurable, hfin⟩
    exact hmem.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hWB : ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ ((k : ℝ) * (1 / p)) * Wr p f (2 ^ k) ≤ B :=
    fun k hk => wr_le_of_besov hq0 hp.le hf hB0 hbes hfin k hk
  have hNp : (Np p f (Icc 0 1)).toReal ≤ B := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((eLpNorm_le_besovNorm (ENNReal.ofReal p) (1 / p) q f).trans hbes)
    rw [ENNReal.toReal_ofReal hB0] at this
    exact this
  have hW2 : (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal ≤ B := by
    have h1 := hWB 1 le_rfl
    have hWr : Wr p f (2 ^ 1) = (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal := by
      unfold Wr; norm_num
    rw [hWr] at h1
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (((1 : ℕ) : ℝ) * (1 / p)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hW0 : 0 ≤ (wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal := ENNReal.toReal_nonneg
    nlinarith
  have hB0bound : B0 p CW f ≤ C0c p CW * B := by
    have := B0_le (p := p) (CW := CW) (B := B) hp.le hCW hf hfin hB0 hNp hW2
    unfold C0c; linarith [this]
  -- termo a termo
  have hterm : ∀ r : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p))) *
          realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
            (2 ^ (r + 1)) f ≤
        (1 + 45 * ENNReal.ofReal CW) *
            besovSeq (ENNReal.ofReal p) (1 / p) f (r + 1) +
          5 * (ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p))) *
            ENNReal.ofReal (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
              (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ))) := by
    intro r
    obtain ⟨hc1, hc2, hc3⟩ := level_conditions hp hCW hB0 (ℓ := r + 1) (by omega) hB0bound
    have hcl := critical_level hp hW hCW hf hfi hfin hB0 hWB (r := r + 1) (by omega)
      (H := criticalAgenda p CW B (2 ^ (r + 1))) hc1 hc2 hc3
    have hω : wtP (ENNReal.ofReal p) (1 / ((2 ^ (r + 1) : ℕ) : ℝ)) f =
        wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ (r + 1)) f := by
      push_cast; rfl
    rw [hω] at hcl
    set a : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p))) with ha
    calc a * realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
            (2 ^ (r + 1)) f
        ≤ a * (wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ (r + 1)) f +
            5 * (9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ (r + 1)) f +
              ENNReal.ofReal (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
                (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hcl (zero_le a)
      _ = (1 + 45 * ENNReal.ofReal CW) * besovSeq (ENNReal.ofReal p) (1 / p) f (r + 1) +
            5 * (a * ENNReal.ofReal (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
                (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ))) := by
          unfold besovSeq
          rw [← ha]
          ring
  -- majorante da parte do erro
  have hE0 : ∀ r : ℕ, 0 ≤ 8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
      (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ) := by
    intro r
    have hB0' : 0 ≤ B0 p CW f := FormalizacaoLow.B0_nonneg p CW f
    have hnum : 0 ≤ B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1 := by
      have : 0 ≤ 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) ≤ 144 * CW * (2 : ℝ) ^ (1 / p) := by
          have := (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / p)); exact mul_nonneg (by linarith) this
        exact mul_nonneg (mul_nonneg h1 hB0) (by positivity)
      linarith
    apply div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hYw : ∀ r : ℕ, 5 * (ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p))) *
      ENNReal.ofReal (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
        (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ))) ≤
      ENNReal.ofReal (Cw * σ ^ r) := by
    intro r
    have hH : Avc p CW * (B + 1) * (((2 ^ (r + 1) : ℕ) : ℝ) + 1) ≤
        (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ) := by
      unfold criticalAgenda; exact Nat.le_ceil _
    have hE := E_majorant hp hCW hB0 r hB0bound hH
    have ha0 : 0 ≤ (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p)) := by positivity
    have hE0' := hE0 r
    have hE' : (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p)) *
        (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
          (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ)) ≤
        Kmaj * (((r : ℝ) + 2) * ρ ^ r) := hE
    have e5 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        (5 : ℝ≥0∞) * (ENNReal.ofReal x * ENNReal.ofReal y) = ENNReal.ofReal (5 * (x * y)) := by
      intro x y hx hy
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), ENNReal.ofReal_mul hx,
        ENNReal.ofReal_ofNat]
    rw [e5 _ _ ha0 hE0']
    apply ENNReal.ofReal_le_ofReal
    have hgeo := hK' r
    calc 5 * ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p)) *
          (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
            (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ)))
        ≤ 5 * (Kmaj * (((r : ℝ) + 2) * ρ ^ r)) := mul_le_mul_of_nonneg_left hE' (by norm_num)
      _ ≤ 5 * (Kmaj * (K' * σ ^ r)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hgeo hKmaj0
      _ = Cw * σ ^ r := by rw [hCw]; ring
  -- soma em ℓ^q
  have hc45 : (1 : ℝ≥0∞) + 45 * ENNReal.ofReal CW ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  set X : ℕ → ℝ≥0∞ := fun r => (1 + 45 * ENNReal.ofReal CW) *
    besovSeq (ENNReal.ofReal p) (1 / p) f (r + 1) with hXdef
  set Yf : ℕ → ℝ≥0∞ := fun r => 5 * (ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p))) *
      ENNReal.ofReal (8 * (B0 p CW f + 144 * CW * (2 : ℝ) ^ (1 / p) * B * ((r + 1 : ℕ) : ℝ) + 1) /
        (criticalAgenda p CW B (2 ^ (r + 1)) : ℝ))) with hYfdef
  have hlq1 := lq_mono hq0 hterm
  have hlq2 := lqNorm_add_le hq0 hqt X Yf
  have hlqX : lqNorm q X ≤ ENNReal.ofReal ((1 + 45 * CW) * B) := by
    have hsh : lqNorm q (fun r => besovSeq (ENNReal.ofReal p) (1 / p) f (r + 1)) ≤ ENNReal.ofReal B :=
      (lq_shift_le hq0 _).trans ((lqNorm_le_besovNorm _ _ _ f).trans hbes)
    have hc : (1 + 45 * ENNReal.ofReal CW) = ENNReal.ofReal (1 + 45 * CW) := by
      rw [ENNReal.ofReal_add (by norm_num) (by linarith), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_one]
    have hX' : X = fun r => (1 + 45 * ENNReal.ofReal CW) *
        besovSeq (ENNReal.ofReal p) (1 / p) f (r + 1) := rfl
    rw [hX', lqNorm_const_mul hq0 hc45, hc]
    calc ENNReal.ofReal (1 + 45 * CW) * lqNorm q (fun r => besovSeq (ENNReal.ofReal p) (1 / p) f (r + 1))
        ≤ ENNReal.ofReal (1 + 45 * CW) * ENNReal.ofReal B := mul_le_mul_of_nonneg_left hsh (zero_le _)
      _ = ENNReal.ofReal ((1 + 45 * CW) * B) := (ENNReal.ofReal_mul (by linarith)).symm
  have hlqY : lqNorm q Yf ≤ ENNReal.ofReal Dw :=
    (lq_mono hq0 (fun r => hYw r)).trans hDw.le
  calc lqNorm q (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 / p))) *
        realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
          (2 ^ (r + 1)) f)
      ≤ lqNorm q (fun r => X r + Yf r) := hlq1
    _ ≤ 2 * ((lqNorm q X) ^ Q + (lqNorm q Yf) ^ Q) ^ Q⁻¹ := hlq2
    _ ≤ 2 * ((ENNReal.ofReal ((1 + 45 * CW) * B)) ^ Q + (ENNReal.ofReal Dw) ^ Q) ^ Q⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (zero_le _)
        apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hQ0.le)
        exact add_le_add (ENNReal.rpow_le_rpow hlqX hQ0.le) (ENNReal.rpow_le_rpow hlqY hQ0.le)
    _ = ENNReal.ofReal (2 * ((((1 + 45 * CW) * B) ^ Q + Dw ^ Q) ^ Q⁻¹)) := by
        have h1 : 0 ≤ (1 + 45 * CW) * B := by positivity
        rw [ENNReal.ofReal_rpow_of_nonneg h1 hQ0.le, ENNReal.ofReal_rpow_of_nonneg hDw0 hQ0.le,
          ← ENNReal.ofReal_add (Real.rpow_nonneg h1 _) (Real.rpow_nonneg hDw0 _),
          ENNReal.ofReal_rpow_of_nonneg (by have := Real.rpow_nonneg h1 Q; have := Real.rpow_nonneg hDw0 Q; linarith)
            (inv_nonneg.mpr hQ0.le),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (2 * ((1 + 45 * CW) ^ Q + Dw ^ Q) ^ Q⁻¹ * (B + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        have hfin := final_real (K₁ := 1 + 45 * CW) (K₂ := Dw) hQ0 h1CW hDw0 hB0
        have h2 := mul_le_mul_of_nonneg_left hfin (by norm_num : (0 : ℝ) ≤ 2)
        calc 2 * (((1 + 45 * CW) * B) ^ Q + Dw ^ Q) ^ Q⁻¹
            ≤ 2 * (((1 + 45 * CW) ^ Q + Dw ^ Q) ^ Q⁻¹ * (B + 1)) := h2
          _ = 2 * ((1 + 45 * CW) ^ Q + Dw ^ Q) ^ Q⁻¹ * (B + 1) := by ring

end FormalizacaoCrit3

namespace FormalizacaoCrit3

open FormalizacaoCrit FormalizacaoCrit2 FormalizacaoLp FormalizacaoLow FormalizacaoRed
open FormalizacaoFloor Artigo FormalizacaoLq FormalizacaoLqAux FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b

/-- **Taxa uniforme crítica.** Para `f` na bola de Besov de raio `B ≥ 1` e `N = 2^r ≥ 2`,
`R_N^{H_B}(f) ≤ C(B+1) N^{-1/p}`, com `C` dependendo de `(p, q, C_W)`. Segue de `critical_lq`,
pois cada termo da sequência `ℓ^q` é limitado pela norma. -/
theorem critical_rate {p CW : ℝ} {q : ℝ≥0∞} (hp : 1 < p) (hW : FormalizacaoCor.WhitneyLp p CW)
    (hCW : 0 ≤ CW) (hq0 : 0 < q) (hqt : q ≠ ⊤) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ (f : ℝ → ℝ) (B : ℝ), Measurable f → 1 ≤ B →
      besovNorm (ENNReal.ofReal p) (1 / p) q f ≤ ENNReal.ofReal B →
      ∀ r : ℕ, 1 ≤ r →
        realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
          (2 ^ r) f ≤ ENNReal.ofReal (Cr * (B + 1) * ((2 : ℝ) ^ r) ^ (-(1 / p))) := by
  obtain ⟨Cq, hCq, hlq⟩ := critical_lq hp hW hCW hq0 hqt
  refine ⟨Cq, hCq, fun f B hf hB1 hbes r hr => ?_⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hterm := (term_le_lqNorm hq0 _ r').trans (hlq f B hf hB1 hbes)
  set x : ℝ := ((r' + 1 : ℕ) : ℝ) * (1 / p) with hx
  have hpos : (0 : ℝ) < (2 : ℝ) ^ x := by positivity
  have hid : ENNReal.ofReal ((2 : ℝ) ^ x) * realP (ENNReal.ofReal p)
      (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M) (2 ^ (r' + 1)) f ≤
      ENNReal.ofReal (Cq * (B + 1)) := hterm
  have hinv : ENNReal.ofReal ((2 : ℝ) ^ x) * ENNReal.ofReal ((2 : ℝ) ^ (-x)) = 1 := by
    rw [← ENNReal.ofReal_mul hpos.le, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero,
      ENNReal.ofReal_one]
  have hR' : realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
      (2 ^ (r' + 1)) f ≤ ENNReal.ofReal ((2 : ℝ) ^ (-x)) * ENNReal.ofReal (Cq * (B + 1)) := by
    calc realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
          (2 ^ (r' + 1)) f
        = ENNReal.ofReal ((2 : ℝ) ^ (-x)) * (ENNReal.ofReal ((2 : ℝ) ^ x) *
          realP (ENNReal.ofReal p) (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M)
            (2 ^ (r' + 1)) f) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal ((2 : ℝ) ^ (-x))), hinv, one_mul]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-x)) * ENNReal.ofReal (Cq * (B + 1)) :=
          mul_le_mul_of_nonneg_left hid (zero_le _)
  have hpow : ((2 : ℝ) ^ (r' + 1)) ^ (-(1 / p)) = (2 : ℝ) ^ (-x) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hx]
    congr 1
    push_cast
    ring
  have hfinal : ENNReal.ofReal ((2 : ℝ) ^ (-x)) * ENNReal.ofReal (Cq * (B + 1)) =
      ENNReal.ofReal (Cq * (B + 1) * ((2 : ℝ) ^ (r' + 1)) ^ (-(1 / p))) := by
    rw [hpow, ENNReal.ofReal_mul (mul_nonneg hCq (by linarith)), mul_comm]
  rw [hfinal] at hR'
  exact hR'

/-- **Caracterização com a agenda crítica de raio `B`.** Para `f` mensurável com `‖f‖_B ≤ B`,
`f ∈ B^{1/p}_{p,q}` se e somente se `f ∈ R^{1/p}_q(Σ, H_B)_p`. -/
theorem critical_char_radius {p CW : ℝ} {q : ℝ≥0∞} (hp : 1 < p)
    (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW) (hq0 : 0 < q) (hqt : q ≠ ⊤)
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : 1 ≤ B)
    (hbes : besovNorm (ENNReal.ofReal p) (1 / p) q f ≤ ENNReal.ofReal B) :
    f ∈ besovP (ENNReal.ofReal p) (1 / p) q ↔
      f ∈ stratumP (ENNReal.ofReal p) (1 / p) q (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M) := by
  have hGm : ∀ N, ∀ g ∈ (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M) N, Measurable g :=
    fun N g hg => FormalizacaoLp.measurable_sigma hg
  constructor
  · intro hb
    obtain ⟨Cq, _, hlq⟩ := critical_lq hp hW hCW hq0 hqt
    have hfin : eLpNorm f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) < ⊤ :=
      lt_of_le_of_lt ((eLpNorm_le_besovNorm (ENNReal.ofReal p) (1 / p) q f).trans hbes)
        ENNReal.ofReal_lt_top
    refine ⟨hfin, lt_of_le_of_lt (hlq f B hf hB hbes) ENNReal.ofReal_lt_top⟩
  · intro hs
    exact stratum_subset_besov_conn (p := ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith))
      (fun M => Pendencias.Agenda.Sigma (criticalAgenda p CW B) M) hGm (1 / p) q hq0 hf hs

end FormalizacaoCrit3
