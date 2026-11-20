import Formalizacao.ArithmeticFloor

/-!
# Obstrução geométrica e continuidade Lipschitz da biblioteca (auditoria, Partes II e VII)

Formaliza dois fatos sobre a biblioteca exata `A_{N,H}` (representações admissíveis):

* **Última folha** (`terminal_affine`): a folha mais à direita é `J_{k,2^k-1}` com
  `2^k ≤ H`, logo `g` coincide com um átomo afim em `[1-1/H, 1]`.
* **Lipschitz global** (`classNH_lipschitz`): toda `g ∈ A_{N,H}` é `H`-Lipschitz em `[0,1]`.
  Usa a condição de colagem `WF` (continuidade nas fronteiras compartilhadas).
-/

open MeasureTheory Set
open scoped ENNReal

namespace FormalizacaoAltura

open Artigo

/-! ## Altura dos coeficientes -/

/-- `|q| ≤ H` quando `ht q ≤ H` (numerador e denominador reduzidos). -/
lemma abs_ratCast_le_of_ht {q : ℚ} {H : ℕ} (h : ht q ≤ H) : |(q : ℝ)| ≤ H := by
  have hden : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hnum : (q.num.natAbs : ℝ) ≤ H := by
    exact_mod_cast (le_trans (le_max_left _ _) h)
  have hcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def]
  rw [hcast, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q.den : ℝ)),
    div_le_iff₀ (by positivity)]
  have h1 : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h1]
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  calc (q.num.natAbs : ℝ) ≤ H := hnum
    _ = H * 1 := (mul_one _).symm
    _ ≤ H * (q.den : ℝ) := mul_le_mul_of_nonneg_left hden hH

/-- A inclinação de qualquer átomo de altura `≤ H` tem módulo `≤ H`. -/
lemma abs_slope_le_of_height {a : Atom} {H : ℕ} (h : a.height ≤ H) : |(a.s : ℝ)| ≤ H :=
  abs_ratCast_le_of_ht (le_trans a.ht_s_le_height h)

/-- Um átomo de altura `≤ H` é `H`-Lipschitz. -/
lemma atom_abs_sub_le {a : Atom} {H : ℕ} (h : a.height ≤ H) (x y : ℝ) :
    |a.eval x - a.eval y| ≤ H * |x - y| := by
  have hid : a.eval x - a.eval y = (a.s : ℝ) * (x - y) := by
    simp only [Atom.eval]; ring
  rw [hid, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_slope_le_of_height h) (abs_nonneg _)

/-! ## Células filhas -/

lemma cellIcc_left_child (k : ℕ) (m : ℤ) :
    cellIcc (k + 1) (2 * m) = Icc (cL k m) (cL (k + 1) (2 * m + 1)) := by
  rw [cellIcc_eq, cL_child_left, cR_child_left]

lemma cellIcc_right_child (k : ℕ) (m : ℤ) :
    cellIcc (k + 1) (2 * m + 1) = Icc (cL (k + 1) (2 * m + 1)) (cR k m) := by
  rw [cellIcc_eq, cR_child_right]

/-- À esquerda do ponto médio, a avaliação do nó coincide com a da subárvore esquerda. -/
lemma eval_node_left {k : ℕ} {m : ℤ} {l r : LTree} (h : LTree.WF k m (LTree.node l r)) {x : ℝ}
    (hx : x ∈ cellIcc (k + 1) (2 * m)) :
    (LTree.node l r).eval k m x = l.eval (k + 1) (2 * m) x := by
  rw [cellIcc_left_child] at hx
  simp only [LTree.eval]
  split_ifs with hlt
  · rfl
  · have hxe : x = cL (k + 1) (2 * m + 1) := le_antisymm hx.2 (not_lt.mp hlt)
    have hR := LTree.eval_at_right h.1
    rw [cR_child_left] at hR
    rw [hxe, LTree.eval_at_left h.2.1, hR]
    exact_mod_cast h.2.2.symm

/-- À direita do ponto médio, a avaliação do nó coincide com a da subárvore direita. -/
lemma eval_node_right {k : ℕ} {m : ℤ} {l r : LTree} {x : ℝ}
    (hx : x ∈ cellIcc (k + 1) (2 * m + 1)) :
    (LTree.node l r).eval k m x = r.eval (k + 1) (2 * m + 1) x := by
  rw [cellIcc_right_child] at hx
  simp only [LTree.eval]
  rw [if_neg (not_lt.mpr hx.1)]

/-! ## Lipschitz da avaliação de árvores bem formadas -/

/-- Toda árvore bem formada cujas folhas têm altura `≤ H` avalia-se como função `H`-Lipschitz
em sua célula raiz. A colagem nos pontos médios é o que permite juntar as duas metades. -/
theorem eval_lipschitz {H : ℕ} (T : LTree) :
    ∀ (k : ℕ) (m : ℤ), LTree.WF k m T → (∀ a ∈ T.leaves, a.height ≤ H) →
      ∀ x ∈ cellIcc k m, ∀ y ∈ cellIcc k m,
        |T.eval k m x - T.eval k m y| ≤ H * |x - y| := by
  induction T with
  | leaf a =>
    intro k m _ hl x _ y _
    have ha : a.height ≤ H := hl a (by simp [LTree.leaves])
    simp only [LTree.eval]
    exact atom_abs_sub_le ha x y
  | node l r ihl ihr =>
    intro k m h hl
    have hl' : ∀ a ∈ l.leaves, a.height ≤ H := fun a ha => hl a (by simp [LTree.leaves, ha])
    have hr' : ∀ a ∈ r.leaves, a.height ≤ H := fun a ha => hl a (by simp [LTree.leaves, ha])
    have ord : ∀ x ∈ cellIcc k m, ∀ y ∈ cellIcc k m, x ≤ y →
        |(LTree.node l r).eval k m x - (LTree.node l r).eval k m y| ≤ H * |x - y| := by
      intro x hx y hy hxy
      have hx' : cL k m ≤ x ∧ x ≤ cR k m := by
        have := hx; rw [cellIcc_eq, Set.mem_Icc] at this; exact this
      have hy' : cL k m ≤ y ∧ y ≤ cR k m := by
        have := hy; rw [cellIcc_eq, Set.mem_Icc] at this; exact this
      rcases le_or_gt y (cL (k + 1) (2 * m + 1)) with hyc | hyc
      · -- ambos na metade esquerda
        have hxL : x ∈ cellIcc (k + 1) (2 * m) := by
          rw [cellIcc_left_child]; exact ⟨hx'.1, le_trans hxy hyc⟩
        have hyL : y ∈ cellIcc (k + 1) (2 * m) := by
          rw [cellIcc_left_child]; exact ⟨le_trans hx'.1 hxy, hyc⟩
        rw [eval_node_left h hxL, eval_node_left h hyL]
        exact ihl (k + 1) (2 * m) h.1 hl' x hxL y hyL
      · rcases le_or_gt (cL (k + 1) (2 * m + 1)) x with hcx | hcx
        · -- ambos na metade direita
          have hxR : x ∈ cellIcc (k + 1) (2 * m + 1) := by
            rw [cellIcc_right_child]; exact ⟨hcx, hx'.2⟩
          have hyR : y ∈ cellIcc (k + 1) (2 * m + 1) := by
            rw [cellIcc_right_child]; exact ⟨le_trans hcx hxy, hy'.2⟩
          rw [eval_node_right hxR, eval_node_right hyR]
          exact ihr (k + 1) (2 * m + 1) h.2.1 hr' x hxR y hyR
        · -- cruzamento: x < c < y, com c = ponto médio
          have hxL : x ∈ cellIcc (k + 1) (2 * m) := by
            rw [cellIcc_left_child]; exact ⟨hx'.1, hcx.le⟩
          have hcL : cL (k + 1) (2 * m + 1) ∈ cellIcc (k + 1) (2 * m) := by
            rw [cellIcc_left_child]; exact ⟨hx'.1.trans hcx.le, le_rfl⟩
          have hcR : cL (k + 1) (2 * m + 1) ∈ cellIcc (k + 1) (2 * m + 1) := by
            rw [cellIcc_right_child]; exact ⟨le_rfl, hyc.le.trans hy'.2⟩
          have hyR : y ∈ cellIcc (k + 1) (2 * m + 1) := by
            rw [cellIcc_right_child]; exact ⟨hyc.le, hy'.2⟩
          have A : |(LTree.node l r).eval k m x - (LTree.node l r).eval k m
              (cL (k + 1) (2 * m + 1))| ≤ H * |x - cL (k + 1) (2 * m + 1)| := by
            rw [eval_node_left h hxL, eval_node_left h hcL]
            exact ihl (k + 1) (2 * m) h.1 hl' x hxL _ hcL
          have B : |(LTree.node l r).eval k m (cL (k + 1) (2 * m + 1)) - (LTree.node l r).eval k m y|
              ≤ H * |cL (k + 1) (2 * m + 1) - y| := by
            rw [eval_node_right hcR, eval_node_right hyR]
            exact ihr (k + 1) (2 * m + 1) h.2.1 hr' _ hcR y hyR
          calc |(LTree.node l r).eval k m x - (LTree.node l r).eval k m y|
              ≤ |(LTree.node l r).eval k m x - (LTree.node l r).eval k m
                  (cL (k + 1) (2 * m + 1))| + |(LTree.node l r).eval k m
                  (cL (k + 1) (2 * m + 1)) - (LTree.node l r).eval k m y| := abs_sub_le _ _ _
            _ ≤ H * |x - cL (k + 1) (2 * m + 1)| + H * |cL (k + 1) (2 * m + 1) - y| :=
                add_le_add A B
            _ = H * |x - y| := by
                rw [abs_of_nonpos (by linarith : x - cL (k + 1) (2 * m + 1) ≤ 0),
                  abs_of_nonpos (by linarith : cL (k + 1) (2 * m + 1) - y ≤ 0),
                  abs_of_nonpos (by linarith : x - y ≤ 0)]
                ring
    intro x hx y hy
    rcases le_total x y with hxy | hxy
    · exact ord x hx y hy hxy
    · rw [abs_sub_comm, abs_sub_comm x y]
      exact ord y hy x hx hxy

/-! ## Última folha e Lipschitz da biblioteca -/

/-- Todo átomo de uma árvore é uma de suas folhas: a última folha pertence à lista. -/
lemma lastLeaf_mem_leaves : ∀ T : LTree, T.lastLeaf ∈ T.leaves
  | .leaf a => by simp [LTree.leaves, LTree.lastLeaf]
  | .node _ r => by
      have := lastLeaf_mem_leaves r
      simp [LTree.leaves, LTree.lastLeaf, this]

/-- Na raiz `[0,1]`, a última folha é `J_{k,m}` com `m+1 = 2^k ≤ H`. -/
lemma lastLeaf_pow_le {H : ℕ} {T : LTree} (hT : LTree.WF 0 0 T) (hh : T.maxHeight ≤ H) :
    ((T.lastLeaf.m : ℤ) + 1 = 2 ^ T.lastLeaf.k) ∧ (2 : ℤ) ^ T.lastLeaf.k ≤ H := by
  have hmem := lastLeaf_mem_leaves T
  have hr := (LTree.lastLeaf_right hT).1
  have hc : cR 0 0 = 1 := by norm_num [cR]
  rw [hc] at hr
  have hreal : (T.lastLeaf.m : ℝ) + 1 = 2 ^ T.lastLeaf.k := by
    unfold cR at hr
    have hpos : (0 : ℝ) < 2 ^ T.lastLeaf.k := by positivity
    field_simp at hr
    linarith
  have hint : (T.lastLeaf.m : ℤ) + 1 = 2 ^ T.lastLeaf.k := by exact_mod_cast hreal
  refine ⟨hint, ?_⟩
  have hht := (LTree.le_maxHeight hmem).trans hh
  have hm := T.lastLeaf.m_lt_height
  have hab : (T.lastLeaf.m : ℤ) ≤ |T.lastLeaf.m| := le_abs_self _
  have hnat : |T.lastLeaf.m| = (T.lastLeaf.m.natAbs : ℤ) := Int.abs_eq_natAbs _
  have : (T.lastLeaf.m : ℤ) + 1 ≤ H := by
    have : T.lastLeaf.m.natAbs + 1 ≤ H := le_trans hm hht
    omega
  rw [← hint]; exact this

/-- Teorema da última folha: em `A_{N,H}`, o átomo terminal coincide com `g` em `[1-1/H, 1]`. -/
theorem terminal_affine {H : ℕ} {T : LTree} (hT : LTree.WF 0 0 T) (hh : T.maxHeight ≤ H)
    (hH : 1 ≤ H) :
    ∃ a : Atom, a ∈ T.leaves ∧
      ∀ x ∈ Icc (1 - 1 / (H : ℝ)) 1, T.eval 0 0 x = a.eval x := by
  obtain ⟨hint, hpow⟩ := lastLeaf_pow_le hT hh
  have hmem := lastLeaf_mem_leaves T
  refine ⟨T.lastLeaf, hmem, fun x hx => LTree.eval_leaf hT _ hmem x ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hpowR : (2 : ℝ) ^ T.lastLeaf.k ≤ H := by exact_mod_cast hpow
  have hpos : (0 : ℝ) < 2 ^ T.lastLeaf.k := by positivity
  have hmR : (T.lastLeaf.m : ℝ) + 1 = 2 ^ T.lastLeaf.k := by exact_mod_cast hint
  rw [cellIcc_eq, Set.mem_Icc]
  constructor
  · unfold cL
    have hinv : 1 / (H : ℝ) ≤ 1 / (2 : ℝ) ^ T.lastLeaf.k :=
      one_div_le_one_div_of_le hpos hpowR
    have hsplit : (T.lastLeaf.m : ℝ) / 2 ^ T.lastLeaf.k = 1 - 1 / 2 ^ T.lastLeaf.k := by
      field_simp
      linarith
    rw [hsplit]
    linarith
  · unfold cR
    have hx2' : x ≤ 1 := hx2
    have hc : ((T.lastLeaf.m : ℝ) + 1) / 2 ^ T.lastLeaf.k = 1 := by
      rw [hmR, div_self hpos.ne']
    rw [hc]
    exact hx2'

/-- Lipschitz global da biblioteca: `g ∈ A_{N,H}` satisfaz `|g x - g y| ≤ H |x - y|` em `[0,1]`. -/
theorem classNH_lipschitz {N H : ℕ} {g : ℝ → ℝ} (hg : g ∈ FormalizacaoLp.classNH N H)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |g x - g y| ≤ H * |x - y| := by
  obtain ⟨T, hadm, rfl⟩ := hg
  obtain ⟨hWF, _, hmax⟩ := hadm
  have hroot : cellIcc 0 0 = Icc (0 : ℝ) 1 := by
    simp [cellIcc_eq, cL, cR]
  refine eval_lipschitz T 0 0 hWF (fun a ha => (LTree.le_maxHeight ha).trans hmax) x ?_ y ?_
  · rw [hroot]; exact hx
  · rw [hroot]; exact hy

end FormalizacaoAltura
