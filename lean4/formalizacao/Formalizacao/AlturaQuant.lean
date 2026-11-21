import Formalizacao.LpJackson0
import Formalizacao.AlturaTerminal
import Formalizacao.AlturaCoarse

/-!
# Quantização com salto limitado por `J` (auditoria, Parte V, Lema 5.1)

O lema de quantização do artigo (Lema 4.7), estendido a saltos nodais de tamanho `J`, é o
enunciado `nodal_tree` de `FormalizacaoJ` (que já admite saltos `|y_{n+1} - y_n|` arbitrários,
desde que `2^r (|Δy| + 16(R+1)/H) ≤ H`). Aqui derivamos a forma enunciada no relatório:
`n (J+1) ≤ H` e `8 n ≤ H`, com `n = 2^r`, dão um aproximante `g ∈ A_{n,H}` com erro `≤ 8(M+1)/H`.
-/

open Artigo

namespace FormalizacaoAltura

/-- **Quantização com salto `J` (Lema lp:lem:nodal-jump).** Escolhe-se `Q = 2^e` com
`x < Q ≤ 2x`, `x = H/(16(M+1))`; então `8(M+1)Q ≤ H` e `1/(2Q) ≤ 8(M+1)/H`. Se `r ≤ e`
(caso `n ≤ Q`), vale `nodal_tree_gen`; se `e < r` (caso `n > Q`), vale `nodal_tree_coarse`. -/
theorem quantization_jump {r : ℕ} {M J : ℝ} {y : ℤ → ℝ} (hM : 0 ≤ M)
    (hy : ∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → |y n| ≤ M)
    (hJ : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r → |y (n + 1) - y n| ≤ J)
    {H : ℕ} (hH1 : 8 * (2 : ℝ) ^ r ≤ H) (hH2 : 16 * (M + 1) ≤ H)
    (hH3 : (2 : ℝ) ^ r * (J + 1) ≤ H) :
    ∃ T : LTree, AdmNH (2 ^ r) H T ∧
      ∀ g0 : ℝ → ℝ, (∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → g0 (cL r n) = y n) →
        (∀ n : ℤ, 0 ≤ n → n < 2 ^ r → ∃ α β : ℝ, ∀ x ∈ cellIcc r n, g0 x = α + β * x) →
        ∀ x ∈ cellIcc 0 0, |g0 x - T.eval 0 0 x| ≤ 8 * (M + 1) / H := by
  have hH0 : (0 : ℝ) < H := by
    have : (0 : ℝ) < 8 * (2 : ℝ) ^ r := by positivity
    linarith
  have h2r : (2 : ℝ) ^ r ≤ H := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) r]
  have hkH : r + 1 ≤ H := by
    have h1 : ((r + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ r := by
      have : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
      exact_mod_cast this
    have : ((r + 1 : ℕ) : ℝ) ≤ H := by linarith
    exact_mod_cast this
  have hM1 : (0 : ℝ) < 16 * (M + 1) := by linarith
  -- x = H/(16(M+1)) ≥ 1 e a potência de dois Q = 2^e com x < Q ≤ 2x
  set x : ℝ := H / (16 * (M + 1)) with hx_def
  have hx1 : 1 ≤ x := by rw [hx_def, le_div_iff₀ hM1]; linarith
  obtain ⟨n0, hn0a, hn0b⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
  set e : ℕ := n0 + 1 with he_def
  have hQx : x < (2 : ℝ) ^ e := hn0b
  have hQ2x : (2 : ℝ) ^ e ≤ 2 * x := by rw [he_def, pow_succ]; linarith
  have hQ : 8 * (M + 1) * (2 : ℝ) ^ e ≤ (H : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hQ2x (by linarith : (0 : ℝ) ≤ 8 * (M + 1))
    have hxH : 8 * (M + 1) * (2 * x) = (H : ℝ) := by
      rw [hx_def]; field_simp; ring
    linarith
  have hErr : 1 / (2 * 2 ^ e) ≤ 8 * (M + 1) / H := by
    rw [div_le_div_iff₀ (by positivity) hH0]
    have h := mul_le_mul_of_nonneg_left hQx.le (by linarith : (0 : ℝ) ≤ 16 * (M + 1))
    have hxH : 16 * (M + 1) * x = (H : ℝ) := by rw [hx_def]; field_simp
    nlinarith
  by_cases hre : r ≤ e
  · obtain ⟨T, hT, hg⟩ := FormalizacaoJ.nodal_tree_gen (r := r) (e := e) hre hM hy hQ
    refine ⟨T, hT, fun g0 h1 h2 x hx => (hg g0 h1 h2 x hx).trans (hErr.trans le_rfl)⟩
  · push_neg at hre
    obtain ⟨T, hT, hg⟩ := FormalizacaoJ.nodal_tree_coarse (r := r) (e := e) (J := J) hM hy hJ hQ
      h2r hkH hH3
    refine ⟨T, hT, fun g0 h1 h2 x hx => (hg g0 h1 h2 x hx).trans hErr⟩

end FormalizacaoAltura
