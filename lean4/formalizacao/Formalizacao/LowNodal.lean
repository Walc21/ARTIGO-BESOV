import Pendencias.Jackson
import Formalizacao.Whitney13

/-!
# Regimes `s ≤ 1/p`, parte 1: árvore nodal sem controle dos saltos

Versão do `nodal_tree` para o `Lema lp:lem:nodal-general` do artigo. Dados nodais `y_n`
(`0 ≤ n ≤ 2^r`) com `|y_n| ≤ R`, uma potência `Q = 2^e` com `2^r ≤ 2^e` e `H ≥ 8(R+1)Q`: existe
uma árvore `T` com `≤ 2^r` folhas e altura `≤ H` tal que toda função `g₀`, afim por células
`[n/2^r,(n+1)/2^r]` com `g₀(n/2^r) = y_n`, fica a distância `≤ 1/(2Q)` de `T.eval` em `[0,1]`.
Não se supõe cota para `|y_{n+1} - y_n|`.
-/

open Set
open Artigo Pendencias.Jackson

namespace FormalizacaoJ

lemma nodal_tree_gen {r e : ℕ} (hre : r ≤ e) {R : ℝ} (hR : 0 ≤ R) {y : ℤ → ℝ}
    (hy : ∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → |y n| ≤ R) {H : ℕ}
    (hH : 8 * (R + 1) * 2 ^ e ≤ (H : ℝ)) :
    ∃ T, AdmK 0 0 (2 ^ r) H T ∧
      ∀ g0 : ℝ → ℝ, (∀ n : ℤ, 0 ≤ n → n ≤ 2 ^ r → g0 (cL r n) = y n) →
        (∀ n : ℤ, 0 ≤ n → n < 2 ^ r → ∃ α β : ℝ, ∀ x ∈ cellIcc r n, g0 x = α + β * x) →
        ∀ x ∈ cellIcc 0 0, |g0 x - T.eval 0 0 x| ≤ 1 / (2 * 2 ^ e) := by
  have h2e : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  have h2r_e : (2 : ℝ) ^ r ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) hre
  have hRe : 0 ≤ R * 2 ^ e := by positivity
  have hHe : 8 * (2 : ℝ) ^ e ≤ H := by nlinarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hrlt : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
  have hrle : ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r := by push_cast; rfl
  have hr2R : ((r + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ r := by
    rw [← hrle]; exact_mod_cast hrlt
  have hk : 0 + r + 1 ≤ H := by
    have : ((0 + r + 1 : ℕ) : ℝ) ≤ H := by
      have h1 : ((0 + r + 1 : ℕ) : ℝ) = ((r + 1 : ℕ) : ℝ) := by simp
      rw [h1]; linarith
    exact_mod_cast this
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
    have hb1 : |y (n + 1)| ≤ R := hy (n + 1) (by omega) (by omega)
    have hb0 : |y n| ≤ R := hy n h0 (by omega)
    have hd : |y (n + 1) - y n| ≤ 2 * R := by
      calc |y (n + 1) - y n| ≤ |y (n + 1)| + |y n| := abs_sub _ _
        _ ≤ 2 * R := by linarith
    have hp0 : (0 : ℝ) < 2 ^ r := by positivity
    have he0 : (0 : ℝ) < 2 ^ e := by positivity
    rw [zero_add]
    calc (2 : ℝ) ^ r * (|y (n + 1) - y n| + 1 / 2 ^ e)
        ≤ (2 : ℝ) ^ r * (2 * R + 1 / 2 ^ e) := by gcongr
      _ = 2 * R * 2 ^ r + 2 ^ r / 2 ^ e := by ring
      _ ≤ 2 * R * 2 ^ e + 1 := by
          have h1 : (2 : ℝ) ^ r / 2 ^ e ≤ 1 := by
            rw [div_le_one he0]; exact h2r_e
          have h2 : 2 * R * 2 ^ r ≤ 2 * R * 2 ^ e := by gcongr
          linarith
      _ ≤ H := by nlinarith
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
