import Formalizacao.LowNodal

/-!
# Quantização com salto limitado, caso `Q < 2^r` (Lema lp:lem:nodal-jump, caso `n > Q`)

Dados nodais `y_n` (`0 ≤ n ≤ 2^r`) com `|y_n| ≤ R` e saltos `|y_{n+1} - y_n| ≤ J`, e uma potência
`Q = 2^e` (sem hipótese `r ≤ e`) com `8 (R+1) Q ≤ H` e `2^r (J+1) ≤ H`, a mesma malha de valores
`v_n = b_n/(2Q)` (com `b_n ≡ n mod 2`) dá uma árvore de altura `≤ H` cujo erro é `≤ 1/(2Q)`.
Diferentemente de `nodal_tree_gen`, a altura das inclinações é controlada pelos saltos, não por
`Q ≥ n`: aqui a inclinação `2^r (v_{n+1} - v_n)` é limitada por `2^r (J+1) ≤ H`.
-/

open Set
open Artigo Pendencias.Jackson

namespace FormalizacaoJ

lemma nodal_tree_coarse {r e : ℕ} {R J : ℝ} (hR : 0 ≤ R) {y : ℤ → ℝ}
    (hy : ∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → |y n| ≤ R)
    (hJ : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r → |y (n + 1) - y n| ≤ J) {H : ℕ}
    (hH : 8 * (R + 1) * 2 ^ e ≤ (H : ℝ))
    (hH2r : (2 : ℝ) ^ r ≤ H) (hkH : r + 1 ≤ H)
    (hsl0 : (2 : ℝ) ^ r * (J + 1) ≤ H) :
    ∃ T, AdmK 0 0 (2 ^ r) H T ∧
      ∀ g0 : ℝ → ℝ, (∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → g0 (cL r n) = y n) →
        (∀ n : ℤ, 0 ≤ n → n < 2 ^ r → ∃ α β : ℝ, ∀ x ∈ cellIcc r n, g0 x = α + β * x) →
        ∀ x ∈ cellIcc 0 0, |g0 x - T.eval 0 0 x| ≤ 1 / (2 * 2 ^ e) := by
  have hrlt : r < 2 ^ r := Nat.lt_two_pow_self
  have hrle : ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r := by push_cast; rfl
  have hk : 0 + r + 1 ≤ H := by omega
  have hm : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r → n.natAbs + 1 ≤ H := by
    intro n h0 h1
    have h1' : n.natAbs < 2 ^ r := by
      have : n < ((2 ^ r : ℕ) : ℤ) := by push_cast; exact h1
      omega
    have h2 : ((n.natAbs + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ r := by
      rw [← hrle]; exact_mod_cast h1'
    have h3 : ((n.natAbs + 1 : ℕ) : ℝ) ≤ H := by linarith
    exact_mod_cast h3
  have hsl : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r →
      (2 : ℝ) ^ (0 + r) * (|y (n + 1) - y n| + 1 / 2 ^ e) ≤ H := by
    intro n h0 h1
    have hJn := hJ n h0 h1
    have he1 : (1 : ℝ) / 2 ^ e ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have hin : |y (n + 1) - y n| + 1 / 2 ^ e ≤ J + 1 := by linarith
    have hp0 : (0 : ℝ) ≤ 2 ^ (0 + r) := by positivity
    rw [zero_add] at hp0 ⊢
    calc (2 : ℝ) ^ r * (|y (n + 1) - y n| + 1 / 2 ^ e)
        ≤ (2 : ℝ) ^ r * (J + 1) := mul_le_mul_of_nonneg_left hin hp0
      _ ≤ H := hsl0
  have hgood : GoodVals (vqN y e) r 0 := vqN_good y e r 0
  have hWF := uniformTree_WF (vqN y e) r 0 0 hgood
  refine ⟨uniformTree (vqN y e) r 0 0, ⟨hWF, (uniformTree_numLeaves _ r 0 0).le, ?_⟩, ?_⟩
  · rw [LTree.maxHeight_le_iff]
    intro a ha
    obtain ⟨n, h1, h2, rfl⟩ := uniformTree_leaves _ r 0 0 a ha
    have h1' : 0 ≤ n := by simpa using h1
    have h2' : n < 2 ^ r := by simpa using h2
    exact atom_height_nodal hR (hy n h1' h2'.le) (hy (n + 1) (by omega) (by omega)) hH hk
      (hm n h1' h2') (hsl n h1' h2')
  · intro g0 hg0 hcell x hx
    have hη : ∀ n : ℤ, 2 ^ r * 0 ≤ n → n ≤ 2 ^ r * (0 + 1) →
        |g0 (cL (0 + r) n) - vqN y e n| ≤ 1 / (2 * 2 ^ e) := by
      intro n h1 h2
      have h1' : 0 ≤ n := by simpa using h1
      have h2' : n ≤ 2 ^ r := by simpa using h2
      rw [zero_add, hg0 n h1' h2']
      exact vqN_err y e n
    obtain ⟨n, h1, h2, hxn, hsub, hbd⟩ := uniformTree_error hgood g0 hη x hx
    have h1' : 0 ≤ n := by simpa using h1
    have h2' : n < 2 ^ r := by simpa using h2
    have hxn' : x ∈ cellIcc r n := by simpa using hxn
    obtain ⟨α, β, hαβ⟩ := hcell n h1' h2'
    have hL : cL (0 + r) n ∈ cellIcc r n := by
      rw [zero_add]; simp only [cellIcc, cL, mem_Icc]; refine ⟨le_rfl, ?_⟩
      have : (0 : ℝ) < 2 ^ r := by positivity
      rw [div_le_div_iff_of_pos_right this]; linarith
    have hRt : cR (0 + r) n ∈ cellIcc r n := by
      rw [zero_add]; simp only [cellIcc, cR, mem_Icc]; refine ⟨?_, le_rfl⟩
      have : (0 : ℝ) < 2 ^ r := by positivity
      rw [div_le_div_iff_of_pos_right this]; linarith
    have hpos : cR (0 + r) n - cL (0 + r) n ≠ 0 := by
      unfold cR cL
      have : (0 : ℝ) < 2 ^ (0 + r) := by positivity
      rw [← sub_div]
      simp
    have hlin : g0 x = linInterp g0 (cL (0 + r) n) (cR (0 + r) n) x := by
      unfold linInterp
      rw [hαβ x hxn', hαβ _ hL, hαβ _ hRt]
      field_simp
      ring
    rw [← hlin, sub_self, abs_zero, zero_add] at hbd
    exact hbd

end FormalizacaoJ
