import Formalizacao.LeafFloor
import Formalizacao.MinimaxUpper

/-!
# Teorema 5.2 do artigo

Os pisos pelo número de folhas e pela altura valem para o mesmo supremo minimax.
A cota superior usa a construção diádica da F4.
-/

open scoped ENNReal

namespace FormalizacaoMinimax

open FormalizacaoLeaf

private lemma height_floor_NH {p s : ℝ} {q : ℝ≥0∞}
    (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * (H : ℝ) ^ (-s / aPS p s)) ≤ Dfun p s q N H := by
  by_cases hlow : s < 1 / p
  · rw [aPS_of_lt hlow, show -s / (1 + 1 / p - s) = -(s / (1 + (1 / p - s))) by ring]
    exact dfun_slope_floor hp hs0 hs2 hlow.le hq
  · by_cases hmid : s ≤ 1
    · simpa only [aPS_of_mid (le_of_not_gt hlow) hmid, div_one] using
        dfun_geometric_floor hp hs0 hs2 hq
    · rw [aPS_of_gt hp (lt_of_not_ge hmid), neg_div, div_self hs0.ne']
      refine ⟨1 / 2, by norm_num, fun N H hN hH ↦ ?_⟩
      have heq : (1 / 2 : ℝ) * (H : ℝ) ^ (-(1 : ℝ)) = 1 / (2 * (H : ℝ)) := by
        rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_div]
      rw [heq]
      exact dfun_arithmetic_floor hp hs0 hq (by omega) hH

/-- Cota inferior conjunta, com uma constante uniforme nos dois orçamentos. -/
theorem lower_bound_NH (p s : ℝ) (q : ℝ≥0∞)
    (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / aPS p s))) ≤ Dfun p s q N H := by
  obtain ⟨cN, hcN, hleaves⟩ := leaf_floor_const hp hs0 hs2 hq
  obtain ⟨cH, hcH, hheight⟩ := height_floor_NH hp hs0 hs2 hq
  refine ⟨min cN cH / 2, div_pos (lt_min hcN hcH) (by norm_num), fun N H hN hH ↦ ?_⟩
  let x : ℝ := (N : ℝ) ^ (-s)
  let y : ℝ := (H : ℝ) ^ (-s / aPS p s)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  -- Cada piso entra no mesmo supremo com o seu próprio alvo.
  have hmax : ENNReal.ofReal (max (cN * x) (cH * y)) ≤ Dfun p s q N H := by
    rcases le_total (cN * x) (cH * y) with h | h
    · rw [max_eq_right h]
      exact hheight N H hN hH
    · rw [max_eq_left h]
      exact hleaves N H hN hH
  refine (ENNReal.ofReal_le_ofReal ?_).trans hmax
  calc min cN cH / 2 * (x + y) ≤ (cN * x + cH * y) / 2 := by
        have h := add_le_add
          (mul_le_mul_of_nonneg_right (min_le_left cN cH) hx)
          (mul_le_mul_of_nonneg_right (min_le_right cN cH) hy)
        calc min cN cH / 2 * (x + y) = (min cN cH * x + min cN cH * y) / 2 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right h (by norm_num)
    _ ≤ max (cN * x) (cH * y) := by
      linarith [le_max_left (cN * x) (cH * y), le_max_right (cN * x) (cH * y)]

/-- Teorema 5.2 (`lp:thm:minimax-nh`), em toda a faixa de `p`, `s` e `q`. -/
theorem minimax_nh (p s : ℝ) (q : ℝ≥0∞)
    (hp : 1 ≤ p) (hs0 : 0 < s) (hs2 : s < 2) (hq : 0 < q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N H : ℕ, 2 ≤ N → 2 ≤ H →
      ENNReal.ofReal (c * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / aPS p s))) ≤ Dfun p s q N H ∧
      Dfun p s q N H ≤ ENNReal.ofReal (C * ((N : ℝ) ^ (-s) + (H : ℝ) ^ (-s / aPS p s))) := by
  obtain ⟨c, hc, hlower⟩ := lower_bound_NH p s q hp hs0 hs2 hq
  obtain ⟨C, hC, hupper⟩ := upper_bound_NH p s q hp hs0 hs2 hq
  exact ⟨c, C, hc, hC, fun N H hN hH ↦ ⟨hlower N H hN hH, hupper N H hN hH⟩⟩

end FormalizacaoMinimax
