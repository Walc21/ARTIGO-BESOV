import Pendencias.Jackson
import Formalizacao.Whitney13

/-!
# M8, parte 0: a árvore nodal para `L^p`

Dados nodais `y_n` (`0 ≤ n ≤ 2^r`) com `|y_n| ≤ R`, saltos controlados e `H` grande, existe uma
árvore `T` com `≤ 2^r` folhas e altura `≤ H` (elemento de `A_{2^r,H}`) tal que **toda** função
`g₀` afim por células `[n/2^r,(n+1)/2^r]` com `g₀(n/2^r) = y_n` fica a distância `≤ 8(R+1)/H`
de `T.eval` em `[0,1]`. Aplica-se a `g₀ = Q_n f`.
-/

open Set
open Artigo Pendencias.Jackson

namespace FormalizacaoJ

lemma nodal_tree {r : ℕ} {R : ℝ} (hR : 0 ≤ R) {y : ℤ → ℝ}
    (hy : ∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → |y n| ≤ R) {H : ℕ} (hH : 16 * (R + 1) ≤ (H : ℝ))
    (hk : 0 + r + 1 ≤ H)
    (hm : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r → n.natAbs + 1 ≤ H)
    (hsl : ∀ n : ℤ, 0 ≤ n → n < 2 ^ r →
      (2 : ℝ) ^ (0 + r) * (|y (n + 1) - y n| + 16 * (R + 1) / H) ≤ H) :
    ∃ T, AdmK 0 0 (2 ^ r) H T ∧
      ∀ g0 : ℝ → ℝ, (∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → g0 (cL r n) = y n) →
        (∀ n : ℤ, 0 ≤ n → n < 2 ^ r → ∃ α β : ℝ, ∀ x ∈ cellIcc r n, g0 x = α + β * x) →
        ∀ x ∈ cellIcc 0 0, |g0 x - T.eval 0 0 x| ≤ 8 * (R + 1) / H := by
  obtain ⟨e, he1, he2⟩ := exists_Q hR hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hinv : (1 : ℝ) / 2 ^ e ≤ 16 * (R + 1) / H := by
    rw [div_le_div_iff₀ (by positivity) hH0]; linarith
  have hgood : GoodVals (vqN y e) r 0 := vqN_good y e r 0
  have hWF := uniformTree_WF (vqN y e) r 0 0 hgood
  refine ⟨uniformTree (vqN y e) r 0 0, ⟨hWF, (uniformTree_numLeaves _ r 0 0).le, ?_⟩, ?_⟩
  · rw [LTree.maxHeight_le_iff]
    intro a ha
    obtain ⟨n, h1, h2, rfl⟩ := uniformTree_leaves _ r 0 0 a ha
    have h1' : 0 ≤ n := by simpa using h1
    have h2' : n < 2 ^ r := by simpa using h2
    refine atom_height_nodal hR (hy n h1' h2'.le) (hy (n + 1) (by omega) (by omega)) he1 hk
      (hm n h1' h2') ?_
    refine le_trans ?_ (hsl n h1' h2')
    gcongr
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
    have hpos : cR (0 + r) n - cL (0 + r) n ≠ 0 := by
      unfold cR cL
      have : (0 : ℝ) < 2 ^ (0 + r) := by positivity
      rw [← sub_div]
      simp
    have hL : cL (0 + r) n ∈ cellIcc r n := by
      rw [zero_add]; simp only [cellIcc, cL, cR, mem_Icc]; refine ⟨le_rfl, ?_⟩
      have : (0 : ℝ) < 2 ^ r := by positivity
      rw [div_le_div_iff_of_pos_right this]; linarith
    have hRt : cR (0 + r) n ∈ cellIcc r n := by
      rw [zero_add]; simp only [cellIcc, cL, cR, mem_Icc]; refine ⟨?_, le_rfl⟩
      have : (0 : ℝ) < 2 ^ r := by positivity
      rw [div_le_div_iff_of_pos_right this]; linarith
    have hlin : g0 x = linInterp g0 (cL (0 + r) n) (cR (0 + r) n) x := by
      unfold linInterp
      rw [hαβ x hxn', hαβ _ hL, hαβ _ hRt]
      field_simp
      ring
    have h8 : 1 / (2 * 2 ^ e) ≤ 8 * (R + 1) / H := by
      have : (1 : ℝ) / (2 * 2 ^ e) = (1 / 2 ^ e) / 2 := by field_simp
      rw [this]
      have : 16 * (R + 1) / (H : ℝ) / 2 = 8 * (R + 1) / H := by ring
      linarith
    rw [← hlin, sub_self, abs_zero, zero_add] at hbd
    exact hbd.trans h8

end FormalizacaoJ
