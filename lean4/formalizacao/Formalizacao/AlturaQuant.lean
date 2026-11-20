import Formalizacao.LpJackson0
import Formalizacao.AlturaTerminal

/-!
# Quantização com salto limitado por `J` (auditoria, Parte V, Lema 5.1)

O lema de quantização do artigo (Lema 4.7), estendido a saltos nodais de tamanho `J`, é o
enunciado `nodal_tree` de `FormalizacaoJ` (que já admite saltos `|y_{n+1} - y_n|` arbitrários,
desde que `2^r (|Δy| + 16(R+1)/H) ≤ H`). Aqui derivamos a forma enunciada no relatório:
`n (J+1) ≤ H` e `8 n ≤ H`, com `n = 2^r`, dão um aproximante `g ∈ A_{n,H}` com erro `≤ 8(M+1)/H`.
-/

open Artigo

namespace FormalizacaoAltura

/-- **Quantização com salto `J`.** -/
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
  have h2rN : 2 ^ r ≤ H := by exact_mod_cast h2r
  have hrlt : r < 2 ^ r := Nat.lt_two_pow_self
  have hk : 0 + r + 1 ≤ H := by omega
  have hm : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r → n.natAbs + 1 ≤ H := by
    intro n hn hlt
    have hlt' : n < ((2 ^ r : ℕ) : ℤ) := by push_cast; exact hlt
    have hab : n.natAbs = n.toNat := by omega
    have : n.toNat < 2 ^ r := by omega
    omega
  have hfrac : 16 * (M + 1) / H ≤ 1 := by
    rw [div_le_one hH0]; exact hH2
  have hsl : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r →
      (2 : ℝ) ^ (0 + r) * (|y (n + 1) - y n| + 16 * (M + 1) / H) ≤ H := by
    intro n hn hlt
    have h1 := hJ n hn hlt
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (0 + r) := by positivity
    have h2 : |y (n + 1) - y n| + 16 * (M + 1) / H ≤ J + 1 := by linarith
    have h3 : (2 : ℝ) ^ (0 + r) * (|y (n + 1) - y n| + 16 * (M + 1) / H) ≤
        (2 : ℝ) ^ (0 + r) * (J + 1) :=
      mul_le_mul_of_nonneg_left h2 hpos.le
    have h4 : (2 : ℝ) ^ (0 + r) * (J + 1) ≤ H := by simpa using hH3
    linarith
  have hH16 : (16 : ℝ) * (M + 1) ≤ (H : ℝ) := hH2
  obtain ⟨T, hT, hg⟩ := FormalizacaoJ.nodal_tree (r := r) (R := M) hM hy hH16 hk hm hsl
  refine ⟨T, hT, hg⟩

end FormalizacaoAltura
