import Formalizacao.LpDefs

/-!
# Lemas sobre a norma `ℓ^q` em `ℝ≥0∞` (`lqNorm`)

Usados nas reduções condicionais: monotonia, soma, multiplicação por constante,
sequências com suporte finito e domínio a partir de uma cauda.
Vale `0 < q` (com `q = ∞` tratado pelo supremo).
-/

open scoped ENNReal
open MeasureTheory

namespace FormalizacaoLq

open FormalizacaoLp

/-- Monotonia de `lqNorm` na sequência. -/
theorem lq_mono {q : ℝ≥0∞} (hq : 0 < q) {a b : ℕ → ℝ≥0∞} (h : ∀ k, a k ≤ b k) :
    lqNorm q a ≤ lqNorm q b := by
  unfold lqNorm
  split_ifs with hqt
  · exact iSup_mono h
  · have hp : 0 ≤ q.toReal := ENNReal.toReal_nonneg
    exact ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun k =>
      ENNReal.rpow_le_rpow (h k) hp) (inv_nonneg.2 hp)

/-- O supremo de `a` é majorado pela norma `ℓ^q`. -/
theorem iSup_le_lq {q : ℝ≥0∞} (hq : 0 < q) (a : ℕ → ℝ≥0∞) :
    (⨆ r, a r) ≤ lqNorm q a := by
  unfold lqNorm
  split_ifs with hqt
  · exact le_rfl
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    refine iSup_le fun r => ?_
    have h1 : a r ^ q.toReal ≤ ∑' k, a k ^ q.toReal := ENNReal.le_tsum (f := fun k => a k ^ q.toReal) r
    have h2 := ENNReal.rpow_le_rpow h1 (inv_nonneg.2 hp.le)
    rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one] at h2

/-- `(x+y)^p ≤ 2^p (x^p + y^p)` para `p > 0`. -/
theorem add_rpow_le_two_rpow (x y : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (x + y) ^ p ≤ (2 : ℝ≥0∞) ^ p * (x ^ p + y ^ p) := by
  have key : ∀ u v : ℝ≥0∞, u ≤ v → (u + v) ^ p ≤ (2 : ℝ≥0∞) ^ p * (u ^ p + v ^ p) := by
    intro u v huv
    have h1 : u + v ≤ 2 * v := by
      calc u + v ≤ v + v := add_le_add_left huv v
        _ = 2 * v := by ring
    calc (u + v) ^ p ≤ (2 * v) ^ p := ENNReal.rpow_le_rpow h1 hp.le
      _ = (2 : ℝ≥0∞) ^ p * v ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp.le
      _ ≤ (2 : ℝ≥0∞) ^ p * (u ^ p + v ^ p) := mul_le_mul_left' le_add_self _
  rcases le_total x y with h | h
  · exact key x y h
  · rw [add_comm, add_comm (x ^ p)]
    exact key y x h

/-- Soma: `ℓ^q + ℓ^q ⊆ ℓ^q` (finitude). -/
theorem lq_add_lt_top {q : ℝ≥0∞} (hq : 0 < q) {a b : ℕ → ℝ≥0∞}
    (ha : lqNorm q a < ⊤) (hb : lqNorm q b < ⊤) :
    lqNorm q (fun k => a k + b k) < ⊤ := by
  unfold lqNorm at ha hb ⊢
  split_ifs at ha hb ⊢ with hqt
  · exact lt_of_le_of_lt (iSup_le fun k => add_le_add (le_iSup a k) (le_iSup b k))
      (ENNReal.add_lt_top.2 ⟨ha, hb⟩)
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hA : ∑' k, a k ^ q.toReal < ⊤ := (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).1 ha
    have hB : ∑' k, b k ^ q.toReal < ⊤ := (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).1 hb
    have hS : ∑' k, (a k + b k) ^ q.toReal ≤
        (2 : ℝ≥0∞) ^ q.toReal * (∑' k, a k ^ q.toReal + ∑' k, b k ^ q.toReal) := by
      calc ∑' k, (a k + b k) ^ q.toReal
          ≤ ∑' k, (2 : ℝ≥0∞) ^ q.toReal * (a k ^ q.toReal + b k ^ q.toReal) :=
            ENNReal.tsum_le_tsum fun k => add_rpow_le_two_rpow _ _ hp
        _ = (2 : ℝ≥0∞) ^ q.toReal * ∑' k, (a k ^ q.toReal + b k ^ q.toReal) :=
            ENNReal.tsum_mul_left
        _ = (2 : ℝ≥0∞) ^ q.toReal * (∑' k, a k ^ q.toReal + ∑' k, b k ^ q.toReal) := by
            rw [ENNReal.tsum_add]
    have hfin : (2 : ℝ≥0∞) ^ q.toReal * (∑' k, a k ^ q.toReal + ∑' k, b k ^ q.toReal) < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le (by norm_num))
        (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
    exact (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).2 (lt_of_le_of_lt hS hfin)

/-- Multiplicação por constante finita. -/
theorem lq_const_mul_lt_top {q : ℝ≥0∞} (hq : 0 < q) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    {a : ℕ → ℝ≥0∞} (ha : lqNorm q a < ⊤) :
    lqNorm q (fun k => c * a k) < ⊤ := by
  unfold lqNorm at ha ⊢
  split_ifs at ha ⊢ with hqt
  · exact lt_of_le_of_lt (iSup_le fun k => mul_le_mul_left' (le_iSup a k) c)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) ha)
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hA : ∑' k, a k ^ q.toReal < ⊤ := (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).1 ha
    have hS : ∑' k, (c * a k) ^ q.toReal = c ^ q.toReal * ∑' k, a k ^ q.toReal := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext k
      exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
    rw [hS]
    exact (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).2
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le hc) hA)

/-- Sequências finitamente suportadas, com valores finitos, estão em `ℓ^q`. -/
theorem lq_finsupp_lt_top {q : ℝ≥0∞} (hq : 0 < q) {F : ℕ → ℝ≥0∞} {k1 : ℕ}
    (hF : ∀ k, k1 ≤ k → F k = 0) (hfin : ∀ k, F k ≠ ⊤) :
    lqNorm q F < ⊤ := by
  unfold lqNorm
  split_ifs with hqt
  · refine lt_of_le_of_lt (b := ∑ j ∈ Finset.range k1, F j) (iSup_le fun k => ?_)
      (ENNReal.sum_lt_top.2 fun j _ => lt_top_iff_ne_top.2 (hfin j))
    by_cases hk : k < k1
    · exact Finset.single_le_sum (f := F) (fun i _ => zero_le _)
        (Finset.mem_range.2 hk)
    · rw [hF k (Nat.le_of_not_lt hk)]
      exact zero_le _
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hsum : ∑' k, F k ^ q.toReal = ∑ k ∈ Finset.range k1, F k ^ q.toReal := by
      apply tsum_eq_sum
      intro k hk
      have hk' : k1 ≤ k := by
        by_contra h
        exact hk (Finset.mem_range.2 (Nat.lt_of_not_le h))
      rw [hF k hk', ENNReal.zero_rpow_of_pos hp]
    rw [hsum]
    have hfin' : ∑ k ∈ Finset.range k1, F k ^ q.toReal < ⊤ :=
      ENNReal.sum_lt_top.2 fun j _ => ENNReal.rpow_lt_top_of_nonneg hp.le (hfin j)
    exact (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).2 hfin'

/-- Domínio a partir de uma cauda: se `b_k ≤ X_k` para `k ≥ k1`, `b_k < ∞` para todo `k` e
`X ∈ ℓ^q`, então `b ∈ ℓ^q`. -/
theorem lq_of_eventually_le {q : ℝ≥0∞} (hq : 0 < q) {b X : ℕ → ℝ≥0∞} {k1 : ℕ}
    (hb : ∀ k, b k ≠ ⊤) (hX : lqNorm q X < ⊤) (h : ∀ k, k1 ≤ k → b k ≤ X k) :
    lqNorm q b < ⊤ := by
  set F : ℕ → ℝ≥0∞ := fun k => if k < k1 then b k else 0 with hFdef
  have hF0 : ∀ k, k1 ≤ k → F k = 0 := by
    intro k hk
    simp only [hFdef]
    rw [if_neg (not_lt.2 hk)]
  have hFfin : ∀ k, F k ≠ ⊤ := by
    intro k
    simp only [hFdef]
    split_ifs
    · exact hb k
    · exact ENNReal.zero_ne_top
  have hFlq : lqNorm q F < ⊤ := lq_finsupp_lt_top hq hF0 hFfin
  have hle : ∀ k, b k ≤ X k + F k := by
    intro k
    by_cases hk : k < k1
    · have hFk : F k = b k := by simp only [hFdef]; rw [if_pos hk]
      rw [hFk]
      exact le_add_of_nonneg_left (zero_le _)
    · have hFk : F k = 0 := hF0 k (not_lt.1 hk)
      rw [hFk, add_zero]
      exact h k (not_lt.1 hk)
  exact lt_of_le_of_lt (lq_mono hq hle)
    (lq_add_lt_top hq hX hFlq)

/-- O deslocamento de índice não aumenta a norma `ℓ^q`. -/
theorem lq_shift_le {q : ℝ≥0∞} (hq : 0 < q) (a : ℕ → ℝ≥0∞) :
    lqNorm q (fun k => a (k + 1)) ≤ lqNorm q a := by
  unfold lqNorm
  split_ifs with hqt
  · exact iSup_le fun k => le_iSup a (k + 1)
  · have hp : 0 ≤ q.toReal := ENNReal.toReal_nonneg
    have hinj : Function.Injective (fun k : ℕ => k + 1) := fun x y h => by simpa using h
    exact ENNReal.rpow_le_rpow
      (ENNReal.tsum_comp_le_tsum_of_injective hinj (fun r => a r ^ q.toReal))
      (inv_nonneg.2 hp)

/-- Domínio geométrico: `w_k ≤ C ρ^k` com `0 ≤ ρ < 1` e `q` finito implica `w ∈ ℓ^q`. -/
theorem lq_of_geom_le {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) {w : ℕ → ℝ≥0∞} {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ k, w k ≤ ENNReal.ofReal (C * ρ ^ k)) :
    lqNorm q w < ⊤ := by
  unfold lqNorm
  rw [if_neg hqt]
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
  have hρp : ρ ^ q.toReal < 1 := Real.rpow_lt_one hρ0 hρ1 hp
  have hsum : Summable (fun k : ℕ => C ^ q.toReal * (ρ ^ q.toReal) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hρp).mul_left _
  have e : ∀ k : ℕ, (ρ ^ k) ^ q.toReal = (ρ ^ q.toReal) ^ k := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0, ← Real.rpow_natCast, ← Real.rpow_mul hρ0]
    congr 1
    ring
  have hbound : ∀ k, w k ^ q.toReal ≤ ENNReal.ofReal (C ^ q.toReal * (ρ ^ q.toReal) ^ k) := by
    intro k
    calc w k ^ q.toReal ≤ (ENNReal.ofReal (C * ρ ^ k)) ^ q.toReal :=
          ENNReal.rpow_le_rpow (h k) hp.le
      _ = ENNReal.ofReal ((C * ρ ^ k) ^ q.toReal) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le
      _ = ENNReal.ofReal (C ^ q.toReal * (ρ ^ q.toReal) ^ k) := by
          rw [Real.mul_rpow hC (by positivity), e k]
  have htot : ∑' k, w k ^ q.toReal < ⊤ := by
    calc ∑' k, w k ^ q.toReal ≤ ∑' k, ENNReal.ofReal (C ^ q.toReal * (ρ ^ q.toReal) ^ k) :=
          ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (∑' k, C ^ q.toReal * (ρ ^ q.toReal) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).2 htot

/-- Domínio polinomial: `w_k ≤ D (k+1)^{-κ}` com `κ q > 1` implica `w ∈ ℓ^q`. -/
theorem lq_of_poly_le {q : ℝ≥0∞} (hq : 0 < q) (hqt : q ≠ ⊤) {w : ℕ → ℝ≥0∞} {D κ : ℝ}
    (hD : 0 ≤ D) (hκ : 1 < κ * q.toReal)
    (h : ∀ k, w k ≤ ENNReal.ofReal (D * (((k + 1 : ℕ) : ℝ)) ^ (-κ))) :
    lqNorm q w < ⊤ := by
  unfold lqNorm
  rw [if_neg hqt]
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
  have hsumm : Summable (fun k : ℕ => ((((k + 1 : ℕ) : ℝ)) ^ (κ * q.toReal))⁻¹) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hκ)
  have hsum : Summable (fun k : ℕ => D ^ q.toReal * ((((k + 1 : ℕ) : ℝ)) ^ (κ * q.toReal))⁻¹) :=
    hsumm.mul_left _
  have hbound : ∀ k, w k ^ q.toReal ≤
      ENNReal.ofReal (D ^ q.toReal * ((((k + 1 : ℕ) : ℝ)) ^ (κ * q.toReal))⁻¹) := by
    intro k
    have hx : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
    calc w k ^ q.toReal
        ≤ (ENNReal.ofReal (D * (((k + 1 : ℕ) : ℝ)) ^ (-κ))) ^ q.toReal :=
          ENNReal.rpow_le_rpow (h k) hp.le
      _ = ENNReal.ofReal ((D * (((k + 1 : ℕ) : ℝ)) ^ (-κ)) ^ q.toReal) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le
      _ = ENNReal.ofReal (D ^ q.toReal * ((((k + 1 : ℕ) : ℝ)) ^ (κ * q.toReal))⁻¹) := by
          rw [Real.mul_rpow hD (by positivity), ← Real.rpow_mul hx,
            show -κ * q.toReal = -(κ * q.toReal) by ring, Real.rpow_neg hx]
  have htot : ∑' k, w k ^ q.toReal < ⊤ := by
    calc ∑' k, w k ^ q.toReal
        ≤ ∑' k, ENNReal.ofReal (D ^ q.toReal * ((((k + 1 : ℕ) : ℝ)) ^ (κ * q.toReal))⁻¹) :=
          ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (∑' k, D ^ q.toReal * ((((k + 1 : ℕ) : ℝ)) ^ (κ * q.toReal))⁻¹) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hp)).2 htot

/-- Cauda deslocada: `k ↦ (if e ≤ k then a (k - e) else 0)` tem norma `ℓ^q` não maior que `a`. -/
theorem lq_tail_le {q : ℝ≥0∞} (hq : 0 < q) (a : ℕ → ℝ≥0∞) (e : ℕ) :
    lqNorm q (fun k => if e ≤ k then a (k - e) else 0) ≤ lqNorm q a := by
  unfold lqNorm
  split_ifs with hqt
  · refine iSup_le fun k => ?_
    by_cases hk : e ≤ k
    · simp only [if_pos hk]
      exact le_iSup a (k - e)
    · simp only [if_neg hk]
      exact zero_le _
  · have hp : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
    have hinj : Function.Injective (fun j : ℕ => j + e) := fun x y h => by simpa using h
    have hsupp : Function.support (fun k : ℕ => (if e ≤ k then a (k - e) else 0) ^ q.toReal) ⊆
        Set.range (fun j : ℕ => j + e) := by
      intro k hk
      have hk' : e ≤ k := by
        by_contra h
        exact hk (by simp [if_neg h, ENNReal.zero_rpow_of_pos hp])
      exact ⟨k - e, by simp only; omega⟩
    have hreindex := hinj.tsum_eq hsupp
    have hfg : ∀ j : ℕ, (if e ≤ j + e then a (j + e - e) else 0) ^ q.toReal = a j ^ q.toReal := by
      intro j
      rw [if_pos (Nat.le_add_left e j), Nat.add_sub_cancel]
    have hval : ∑' k, (if e ≤ k then a (k - e) else 0) ^ q.toReal =
        ∑' j, a j ^ q.toReal := by
      rw [← hreindex]
      exact tsum_congr hfg
    rw [hval]

end FormalizacaoLq
