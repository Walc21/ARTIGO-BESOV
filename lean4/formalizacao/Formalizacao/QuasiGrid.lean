import Formalizacao.QuasiLocal

/-!
# Quase-interpolante com médias locais (M4, Lema 5.2 do artigo): parte combinatória

Grade `t_j = j/n` (`0 ≤ j ≤ n`), células `I_k = [t_k, t_{k+1}]` (`0 ≤ k < n`) e
`c(j) = min(j, n-1)`. Os valores nodais são `λ_j(g) = (P_{I_{c(j)}} g)(t_j)`, com `P` o
funcional de `QuasiLocal` (núcleo `kL` no extremo esquerdo para `j < n`, `kR` no extremo
direito para `j = n`). O quase-interpolante é

  `Q_n g = Σ_{j=0}^{n} λ_j(g) φ_j`,  `φ_j(x) = max(0, 1 - n|x - t_j|)`.

Provam-se aqui:
* `lam_affine`: `λ_j(a) = a(t_j)` para funções afins `a` (reprodução do Lema 5.1);
* `Q_cell`: em cada célula `I_k`, `Q_n g` é a combinação de exatamente dois termos;
* `Q_affine`: `Q_n a = a` em cada célula, para `a` afim (Lema 5.2(a)).

A parte de norma `L^p` do Lema 5.2(b) (`‖f - Q_n f‖_{L^p(I_k)} ≤ 9 E(f, J_k)_p`) não está
formalizada aqui.
-/

open MeasureTheory Set

namespace FormalizacaoGrid

open FormalizacaoQuasi

/-- Nó `t_j = j/n`. -/
noncomputable def tn (n j : ℕ) : ℝ := (j : ℝ) / n

/-- Chapéu de nó `t_j`: `φ_j(x) = max(0, 1 - n|x - t_j|)`. -/
noncomputable def hat (n j : ℕ) (x : ℝ) : ℝ := max 0 (1 - |x - tn n j| * n)

/-- Célula `I_k = [t_k, t_{k+1}]`. -/
def cell (n k : ℕ) : Set ℝ := Icc (tn n k) (tn n (k + 1))

/-- Valor nodal `λ_j(g)`: `(P_{I_{c(j)}} g)(t_j)`, com `P` dado pelo núcleo do extremo
esquerdo (`j < n`) ou direito (`j = n`) da célula `c(j) = min(j, n-1)`. -/
noncomputable def lam (n : ℕ) (g : ℝ → ℝ) (j : ℕ) : ℝ :=
  if j < n then ∫ y in cell n j, kL (tn n j) (1 / n) y * g y
  else ∫ y in cell n (n - 1), kR (tn n (n - 1)) (1 / n) y * g y

/-- Quase-interpolante `Q_n g`. -/
noncomputable def Q (n : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), lam n g j * hat n j x

/-- `t_{j+1} - t_j = 1/n` para `n ≥ 1`. -/
lemma tn_succ (n j : ℕ) (hn : 1 ≤ n) : tn n (j + 1) = tn n j + 1 / n := by
  unfold tn
  push_cast
  ring

/-- `λ_j` reproduz funções afins: `λ_j(α + β·) = α + β t_j`. -/
theorem lam_affine {n : ℕ} (hn : 1 ≤ n) (α β : ℝ) (j : ℕ) (hj : j ≤ n) :
    lam n (fun y => α + β * y) j = α + β * tn n j := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  unfold lam
  split_ifs with hjn
  · -- extremo esquerdo `t_j` da célula `j`
    have hint : ∫ y in cell n j, kL (tn n j) (1 / n) y * (α + β * y) =
        ∫ y in tn n j..tn n j + 1 / n, kL (tn n j) (1 / n) y * (α + β * y) := by
      unfold cell
      rw [tn_succ n j hn, intervalIntegral.integral_of_le (by
        have : 0 ≤ 1 / (n : ℝ) := by positivity
        linarith), integral_Icc_eq_integral_Ioc]
    rw [hint]
    exact integral_kL_mul_affine (tn n j) (1 / n) α β (by positivity)
  · -- extremo direito `t_n = 1` da célula `n - 1`
    have hjeq : j = n := by omega
    rw [hjeq]
    have hn1 : n - 1 + 1 = n := by omega
    have hcell : tn n (n - 1) + 1 / n = tn n n := by
      have := tn_succ n (n - 1) hn
      rw [hn1] at this
      linarith
    have hle : tn n (n - 1) ≤ tn n (n - 1) + 1 / n := by
      have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
    have hint : ∫ y in cell n (n - 1), kR (tn n (n - 1)) (1 / n) y * (α + β * y) =
        ∫ y in tn n (n - 1)..tn n (n - 1) + 1 / n, kR (tn n (n - 1)) (1 / n) y * (α + β * y) := by
      unfold cell
      rw [hn1, ← hcell, intervalIntegral.integral_of_le hle, integral_Icc_eq_integral_Ioc]
    rw [hint, integral_kR_mul_affine (tn n (n - 1)) (1 / n) α β (by positivity), hcell]

/-- `t` é monótona em `j`. -/
lemma tn_mono (n : ℕ) {i j : ℕ} (h : i ≤ j) : tn n i ≤ tn n j := by
  unfold tn
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast h

/-- Para `n ≥ 1`, `t_{j} - t_i ≥ (j - i)/n` quando `i ≤ j`. -/
lemma tn_sub_ge (n : ℕ) (hn : 1 ≤ n) {i j : ℕ} (h : i + 1 ≤ j) :
    1 / (n : ℝ) ≤ tn n j - tn n i := by
  have h1 : tn n (i + 1) ≤ tn n j := tn_mono n h
  have h2 : tn n (i + 1) = tn n i + 1 / n := tn_succ n i hn
  linarith

/-- No interior da célula `I_k`, `φ_k` e `φ_{k+1}` são as funções lineares de interpolação. -/
lemma hat_left_of_mem {n k : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ cell n k) :
    hat n k x = (tn n (k + 1) - x) * n := by
  obtain ⟨h1, h2⟩ := hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsucc := tn_succ n k hn
  have hx1 : |x - tn n k| = x - tn n k := abs_of_nonneg (by linarith)
  have hle : (x - tn n k) * n ≤ 1 := by
    have : (tn n (k + 1) - x) * n ≥ 0 := mul_nonneg (by linarith) hn'.le
    have e : (tn n (k + 1) - x) * n = 1 - (x - tn n k) * n := by
      rw [hsucc]; field_simp; ring
    linarith
  unfold hat
  rw [hx1]
  rw [max_eq_right]
  · have e : (tn n (k + 1) - x) * n = 1 - (x - tn n k) * n := by
      rw [hsucc]; field_simp; ring
    linarith
  · linarith

lemma hat_right_of_mem {n k : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ cell n k) :
    hat n (k + 1) x = (x - tn n k) * n := by
  obtain ⟨h1, h2⟩ := hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsucc := tn_succ n k hn
  have hx1 : |x - tn n (k + 1)| = tn n (k + 1) - x := by
    rw [abs_of_nonpos (by linarith)]; ring
  have e : (x - tn n k) * n = 1 - (tn n (k + 1) - x) * n := by
    rw [hsucc]; field_simp; ring
  have hle : (tn n (k + 1) - x) * n ≤ 1 := by
    have : (x - tn n k) * n ≥ 0 := mul_nonneg (by linarith) hn'.le
    linarith
  unfold hat
  rw [hx1, max_eq_right]
  · linarith
  · linarith

/-- Fora de `{k, k+1}` os chapéus se anulam em `I_k`. -/
lemma hat_zero_of_far {n k j : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ cell n k)
    (hj : j ≠ k ∧ j ≠ k + 1) : hat n j x = 0 := by
  obtain ⟨h1, h2⟩ := hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold hat
  have hone : 1 / (n : ℝ) * n = 1 := by field_simp
  apply max_eq_left
  rcases Nat.lt_or_ge j k with hjk | hjk
  · -- j < k: x - t_j ≥ t_k - t_j ≥ 1/n
    have h3 := tn_sub_ge n hn (i := j) (j := k) hjk
    have hpos : 0 < 1 / (n : ℝ) := by positivity
    have hxj : |x - tn n j| = x - tn n j := abs_of_nonneg (by linarith)
    rw [hxj]
    have hA : 1 / (n : ℝ) ≤ x - tn n j := by linarith
    have hB := mul_le_mul_of_nonneg_right hA hn'.le
    linarith
  · -- j ≥ k + 2: t_j - x ≥ t_{k+1} + 1/n - x ≥ 1/n
    have hjk2 : k + 2 ≤ j := by omega
    have h3 := tn_sub_ge n hn (i := k + 1) (j := j) (by omega)
    have hxj : |x - tn n j| = tn n j - x := by
      rw [abs_of_nonpos (by linarith [tn_mono n (show k + 1 ≤ j by omega)])]
      ring
    rw [hxj]
    have hA : 1 / (n : ℝ) ≤ tn n j - x := by linarith
    have hB := mul_le_mul_of_nonneg_right hA hn'.le
    linarith

/-- Em `I_k` (`k < n`), o quase-interpolante usa exatamente dois termos. -/
theorem Q_cell {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) (g : ℝ → ℝ) {x : ℝ} (hx : x ∈ cell n k) :
    Q n g x = lam n g k * hat n k x + lam n g (k + 1) * hat n (k + 1) x := by
  unfold Q
  have hsub : ({k, k + 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_pair (by omega)]
  · intro j _ hj
    have hj' : j ≠ k ∧ j ≠ k + 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact hj
    rw [hat_zero_of_far hn hx hj', mul_zero]

/-- Lema 5.2(a) localmente: `Q_n a = a` em cada célula, para `a` afim. -/
theorem Q_affine {n k : ℕ} (hn : 1 ≤ n) (hk : k < n) (α β : ℝ) {x : ℝ} (hx : x ∈ cell n k) :
    Q n (fun y => α + β * y) x = α + β * x := by
  rw [Q_cell hn hk _ hx, lam_affine hn α β k (by omega), lam_affine hn α β (k + 1) (by omega),
    hat_left_of_mem hn hx, hat_right_of_mem hn hx]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hsucc := tn_succ n k hn
  rw [hsucc]
  field_simp
  ring

/-- Célula do valor nodal `λ_j`: `c(j) = min(j, n-1)`. -/
def cellIdx (n j : ℕ) : ℕ := min j (n - 1)

/-- `λ_j` é a cota de Hölder do Lema 5.1 na célula `I_{c(j)}`, com `ℓ = 1/n`:
`|λ_j(g)| ≤ 4 n^{1/p} ‖g‖_{L^p(I_{c(j)})}`. -/
theorem abs_lam_le {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (j : ℕ) (hj : j ≤ n)
    (hgm : Measurable g)
    (hfin : eLpNorm g (ENNReal.ofReal p) (volume.restrict (cell n (cellIdx n j))) < ⊤) :
    |lam n g j| ≤ 4 * (n : ℝ) ^ (1 / p) *
      (eLpNorm g (ENNReal.ofReal p) (volume.restrict (cell n (cellIdx n j)))).toReal := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ : (0 : ℝ) < 1 / n := by positivity
  have hpow : (1 / (n : ℝ)) ^ (-(1 / p)) = (n : ℝ) ^ (1 / p) := by
    rw [Real.div_rpow zero_le_one hn'.le, Real.one_rpow, Real.rpow_neg hn'.le]
    simp
  unfold lam
  split_ifs with hjn
  · -- célula `j`, extremo esquerdo `t_j = a`, `ℓ = 1/n`
    have hcell : cell n j = Icc (tn n j) (tn n j + 1 / n) := by
      unfold cell; rw [tn_succ n j hn]
    have hci : cellIdx n j = j := by unfold cellIdx; omega
    rw [hci] at hfin ⊢
    rw [hcell] at hfin ⊢
    have hb := abs_integral_kernel_le (a := tn n j) (ℓ := 1 / n) hℓ (p := p) hp
      (k := kL (tn n j) (1 / n)) (h := g)
      (fun y hy => abs_kL_le hℓ hy)
      (by unfold kL; fun_prop) hgm.aestronglyMeasurable hfin
    rw [hpow] at hb
    exact hb
  · -- célula `n - 1`, extremo direito `t_n = a + 1/n`
    have hcell : cell n (n - 1) = Icc (tn n (n - 1)) (tn n (n - 1) + 1 / n) := by
      unfold cell
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1]
      congr 1
      have := tn_succ n (n - 1) hn
      rw [hn1] at this
      linarith
    have hci : cellIdx n j = n - 1 := by unfold cellIdx; omega
    rw [hci] at hfin ⊢
    rw [hcell] at hfin ⊢
    have hb := abs_integral_kernel_le (a := tn n (n - 1)) (ℓ := 1 / n) hℓ (p := p) hp
      (k := kR (tn n (n - 1)) (1 / n)) (h := g)
      (fun y hy => abs_kR_le hℓ hy)
      (by unfold kR; fun_prop) hgm.aestronglyMeasurable hfin
    rw [hpow] at hb
    exact hb

/-- **Lema 5.2(c).** `|λ_j(g)| ≤ 2 sup_{I_{c(j)}} |g|`. -/
theorem abs_lam_sup_le {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (j : ℕ) (hj : j ≤ n)
    (hgb : ∀ y ∈ cell n (cellIdx n j), |g y| ≤ M) :
    |lam n g j| ≤ 2 * M := by
  have hℓ : (0 : ℝ) < 1 / n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  unfold lam
  split_ifs with hjn
  · have hci : cellIdx n j = j := by unfold cellIdx; omega
    rw [hci] at hgb
    have hcell : cell n j = Icc (tn n j) (tn n j + 1 / n) := by
      unfold cell; rw [tn_succ n j hn]
    rw [hcell] at hgb ⊢
    exact abs_integral_kL_mul_le hℓ hM hgb
  · have hci : cellIdx n j = n - 1 := by unfold cellIdx; omega
    rw [hci] at hgb
    have hcell : cell n (n - 1) = Icc (tn n (n - 1)) (tn n (n - 1) + 1 / n) := by
      unfold cell
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1]
      congr 1
      have := tn_succ n (n - 1) hn
      rw [hn1] at this
      linarith
    rw [hcell] at hgb ⊢
    exact abs_integral_kR_mul_le hℓ hM hgb

end FormalizacaoGrid
