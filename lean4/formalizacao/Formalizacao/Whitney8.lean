import Formalizacao.Whitney7

/-!
# Whitney em `L^p` (M5), parte 8: soma nas células

Cada ponto pertence a no máximo `4` dos conjuntos `J_k` (três para `k ≤ n-2`, mais `J_{n-1}`).
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid
open scoped Classical

namespace FormalizacaoW

open FormalizacaoCor

/-- multiplicidade dos `J_k`: no máximo `4` -/
lemma card_mem_le {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    (Finset.filter (fun k => x ∈ Jcell n k) (Finset.range n)).card ≤ 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set S := Finset.filter (fun k => x ∈ Jcell n k) (Finset.range n) with hS
  set T := S.filter (fun k => k ≤ n - 2) with hT
  have hsub : S ⊆ T ∪ {n - 1} := by
    intro k hk
    by_cases h : k ≤ n - 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hk, h⟩)
    · have : k < n := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
      have : k = n - 1 := by omega
      exact Finset.mem_union_right _ (by simp [this])
  -- para `k ≤ n-2`, `x ∈ J_k ↔ k/n ≤ x ≤ (k+2)/n`
  have hmem : ∀ k ∈ T, (k : ℝ) / n ≤ x ∧ x ≤ ((k : ℝ) + 2) / n := by
    intro k hk
    have hk1 := (Finset.mem_filter.1 hk)
    have hkle : k ≤ n - 2 := hk1.2
    have hx := (Finset.mem_filter.1 hk1.1).2
    unfold Jcell at hx
    have hmin : min k (n - 2) = k := min_eq_left hkle
    rw [hmin] at hx
    unfold tn at hx
    push_cast at hx
    exact hx
  have hT3 : T.card ≤ 3 := by
    by_cases hne : T.Nonempty
    · set k0 := T.min' hne with hk0
      have hsubT : T ⊆ Finset.Icc k0 (k0 + 2) := by
        intro k hk
        rw [Finset.mem_Icc]
        refine ⟨T.min'_le k hk, ?_⟩
        have h1 := (hmem k hk).1
        have h2 := (hmem k0 (T.min'_mem hne)).2
        have : (k : ℝ) / n ≤ ((k0 : ℝ) + 2) / n := h1.trans h2
        rw [div_le_div_iff_of_pos_right hn'] at this
        have : (k : ℝ) ≤ ((k0 + 2 : ℕ) : ℝ) := by push_cast; exact this
        exact_mod_cast this
      calc T.card ≤ (Finset.Icc k0 (k0 + 2)).card := Finset.card_le_card hsubT
        _ = 3 := by simp; omega
    · simp [Finset.not_nonempty_iff_eq_empty.1 hne]
  calc S.card ≤ (T ∪ {n - 1}).card := Finset.card_le_card hsub
    _ ≤ T.card + ({n - 1} : Finset ℕ).card := Finset.card_union_le _ _
    _ ≤ 3 + 1 := by simp; omega
    _ = 4 := rfl

/-- soma de integrais sobre `S_k ⊆ J_k`: `Σ_k ∫_{S_k} F ≤ 4 ∫_U F`. -/
lemma sum_lintegral_le {n : ℕ} (hn : 2 ≤ n) {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {S : ℕ → Set ℝ} (hSm : ∀ k, MeasurableSet (S k)) (hSJ : ∀ k, k < n → S k ⊆ Jcell n k)
    {U : Set ℝ} (hUm : MeasurableSet U) (hSU : ∀ k, k < n → S k ⊆ U) :
    ∑ k ∈ Finset.range n, ∫⁻ x in S k, F x ≤ 4 * ∫⁻ x in U, F x := by
  have h1 : ∑ k ∈ Finset.range n, ∫⁻ x in S k, F x =
      ∫⁻ x, ∑ k ∈ Finset.range n, (S k).indicator F x := by
    rw [lintegral_finset_sum _ (fun k _ => hF.indicator (hSm k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [lintegral_indicator (hSm k)]
  rw [h1, ← lintegral_indicator hUm, ← lintegral_const_mul _ (hF.indicator hUm)]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    have hsum : ∑ k ∈ Finset.range n, (S k).indicator F x =
        ((Finset.filter (fun k => x ∈ S k) (Finset.range n)).card : ℝ≥0∞) * F x := by
      simp only [Set.indicator_apply]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hc : (Finset.filter (fun k => x ∈ S k) (Finset.range n)).card ≤ 4 := by
      refine le_trans (Finset.card_le_card ?_) (card_mem_le hn x)
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hSJ k (Finset.mem_range.1 hk.1) hk.2⟩
    gcongr
    exact_mod_cast hc
  · have : ∑ k ∈ Finset.range n, (S k).indicator F x = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      exact Set.indicator_of_notMem (fun h => hx (hSU k (Finset.mem_range.1 hk) h)) _
    rw [this]; exact zero_le _

end FormalizacaoW
