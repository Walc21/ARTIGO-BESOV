import Formalizacao.Lemma55c

/-!
# Lema 5.5 (M6), parte (b): cota do módulo de continuidade de `G`

`F r = Q_{2^{r+1}} f`. Por indução, `F r` é afim em cada célula de malha `2^{-(r+1)}`, com
inclinação de módulo no máximo `M r` (recursão `M 0 = Λ_0`, `M (r+1) = M r + K' 2^{(r+1)(1-s')}`).
-/

open scoped ENNReal
open Filter Topology
open MeasureTheory Set FormalizacaoLp FormalizacaoGrid FormalizacaoL55 FormalizacaoL55b FormalizacaoL55c

namespace FormalizacaoL55d

/-- Constante de inclinação `K' = 144 C_W S 2^{1/p+1}`. -/
noncomputable def Kslope (p CW : ℝ) (S : ℝ≥0∞) : ℝ := 144 * CW * S.toReal * (2 : ℝ) ^ (1 / p + 1)

/-- Constante `Λ_0` da inclinação de `F 0 = Q_2 f`. -/
noncomputable def Lam0 (p CW : ℝ) (f : ℝ → ℝ) : ℝ :=
  8 * (1 / (2 : ℝ)) ^ (-(1 / p) - 1) *
    (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal

/-- Sequência de cotas de inclinação. -/
noncomputable def Mseq (p s CW : ℝ) (S : ℝ≥0∞) (f : ℝ → ℝ) : ℕ → ℝ
  | 0 => Lam0 p CW f
  | r + 1 => Mseq p s CW S f r + Kslope p CW S * (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 - (s - 1 / p)))

/-- `F_0 = Q_2 f` tem inclinação limitada por `Λ_0` nas células de malha `1/2`. -/
theorem F0_slope {p CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) (j : ℕ) (hj : j < 2) :
    ∃ α β : ℝ, (∀ x ∈ cell 2 j, Q 2 f x = α + β * x) ∧
      |β| ≤ Lam0 p CW f := by
  have hQ : Np p (Q 2 f) (Icc 0 1) < ⊤ := by
    have hpos := Np_Q_le (n := 2) hp hf
    have hd := FormalizacaoCor.quasi_error hp hW (show 2 ≤ 2 by norm_num) hf hfi hfin
    have hω : wtP (ENNReal.ofReal p) (1 / ((2 : ℕ) : ℝ)) f < ⊤ := by
      have := wtP_lt_top hp hf hfin 2
      simpa using this
    refine lt_of_le_of_lt (le_trans hpos (add_le_add le_rfl (by simpa using hd))) ?_
    refine ENNReal.add_lt_top.2 ⟨hfin, ?_⟩
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) ?_
    simpa using hω
  have hv : ∀ i, i < 2 → ∃ α β : ℝ, ∀ x ∈ cell 2 i, Q 2 f x = α + β * x := fun i hi => by
    obtain ⟨a, b, h⟩ := Q_affine_on_cell (n := 2) (by norm_num) hi f
    exact ⟨a, b, h⟩
  obtain ⟨β, hβ, α, hab⟩ := slope_le_of_affine_cells (N := 2) hp (le_refl 2) hv hQ hj
  refine ⟨α, β, hab, ?_⟩
  have hbd : (Np p (Q 2 f) (Icc 0 1)).toReal ≤
      (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal := by
    have hpos := Np_Q_le (n := 2) hp hf
    have hd := FormalizacaoCor.quasi_error hp hW (show 2 ≤ 2 by norm_num) hf hfi hfin
    have hsum_fin : Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨hfin.ne, ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) ?_⟩
      simpa using (wtP_lt_top hp hf hfin 2).ne
    exact ENNReal.toReal_mono hsum_fin (le_trans hpos (add_le_add le_rfl (by simpa using hd)))
  have hc : (0 : ℝ) ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p) - 1) := by positivity
  have hβ' : |β| ≤ 8 * (1 / (2 : ℝ)) ^ (-(1 / p) - 1) *
      (Np p f (Icc 0 1) + 9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ)) f).toReal := by
    have h2 : (1 / ((2 : ℕ) : ℝ)) = (1 / (2 : ℝ)) := by norm_num
    simp only [h2] at hβ
    exact hβ.trans (mul_le_mul_of_nonneg_left hbd hc)
  unfold Lam0
  exact hβ'

/-- **Indução:** `F_r` é afim em cada célula de malha `2^{-(r+1)}`, com inclinação `≤ M r`. -/
theorem F_affine_cells {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (r : ℕ) :
    ∀ j, j < 2 ^ (r + 1) → ∃ α β : ℝ,
      (∀ x ∈ cell (2 ^ (r + 1)) j, FormalizacaoL55c.F f r x = α + β * x) ∧
      |β| ≤ Mseq p s CW S f r := by
  induction r with
  | zero =>
    intro j hj
    obtain ⟨α, β, hab, hβ⟩ := F0_slope hp hW hCW hf hfi hfin j hj
    exact ⟨α, β, hab, hβ⟩
  | succ r ih =>
    intro j hj
    have hr : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
    have hj2 : j / 2 < 2 ^ (r + 1) := by
      have h : 2 ^ (r + 1 + 1) = 2 * 2 ^ (r + 1) := by ring
      rw [h] at hj
      omega
    obtain ⟨a1, b1, h1, hb1⟩ := ih (j / 2) hj2
    obtain ⟨β2, hβ2, α2, h2⟩ := vk_slope_le hp hW hCW hf hfi hfin hS hbS
      (k := r + 1) (by omega) hj
    have hsub : cell (2 ^ (r + 1 + 1)) j ⊆ cell (2 ^ (r + 1)) (j / 2) := by
      have h : 2 ^ (r + 1 + 1) = 2 * 2 ^ (r + 1) := by ring
      rw [h]
      have h' : j < 2 * 2 ^ (r + 1) := by rw [← h]; exact hj
      exact cell_fine_sub_coarse hr h'
    refine ⟨a1 + α2, b1 + β2, fun x hx => ?_, ?_⟩
    · have hxa := h1 x (hsub hx)
      have hxb := h2 x hx
      have e : FormalizacaoL55c.F f (r + 1) x = FormalizacaoL55c.F f r x +
          (Q (2 ^ (r + 1 + 1)) f x - Q (2 ^ (r + 1)) f x) := by
        unfold FormalizacaoL55c.F; ring
      rw [e, hxa, hxb]
      ring
    · have hMs : Mseq p s CW S f (r + 1) = Mseq p s CW S f r + Kslope p CW S *
          (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 - (s - 1 / p))) := rfl
      rw [hMs]
      calc |b1 + β2| ≤ |b1| + |β2| := abs_add_le _ _
        _ ≤ Mseq p s CW S f r + Kslope p CW S * (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 - (s - 1 / p))) := by
            apply add_le_add hb1
            unfold Kslope
            exact hβ2

/-- `M_r ≥ 0`. -/
theorem Mseq_nonneg {p s CW : ℝ} (f : ℝ → ℝ) (S : ℝ≥0∞) (hLam : 0 ≤ Lam0 p CW f)
    (hK : 0 ≤ Kslope p CW S) (r : ℕ) : 0 ≤ Mseq p s CW S f r := by
  induction r with
  | zero => exact hLam
  | succ r ih =>
    show 0 ≤ Mseq p s CW S f r + Kslope p CW S * (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 - (s - 1 / p)))
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * (1 - (s - 1 / p))) := by positivity
    exact add_nonneg ih (mul_nonneg hK this)

/-- Dentro de uma célula de `F_r`, `|F u - F w| ≤ M|u-w|`. -/
theorem cell_lip {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (r : ℕ) {i : ℕ} (hi : i < 2 ^ (r + 1)) {u w : ℝ}
    (hu : u ∈ cell (2 ^ (r + 1)) i) (hw : w ∈ cell (2 ^ (r + 1)) i) :
    |FormalizacaoL55c.F f r u - FormalizacaoL55c.F f r w| ≤ Mseq p s CW S f r * |u - w| := by
  obtain ⟨α, β, hab, hβ⟩ := F_affine_cells hp hW hCW hf hfi hfin hS hbS hs r i hi
  rw [hab u hu, hab w hw]
  have : α + β * u - (α + β * w) = β * (u - w) := by ring
  rw [this, abs_mul]
  exact mul_le_mul_of_nonneg_right hβ (abs_nonneg _)

/-- **Lipschitz por partes:** para `x ≤ y` em `[0,1]` com `y - x ≤ 2^{-(r+1)}`,
`|F_r y - F_r x| ≤ M_r (y - x)`. -/
theorem F_lip {p s CW : ℝ} (hp : 1 ≤ p) (hW : FormalizacaoCor.WhitneyLp p CW) (hCW : 0 ≤ CW)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {S : ℝ≥0∞} (hS : S < ⊤)
    (hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S)
    (hs : 1 / p < s) (r : ℕ) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) (hd : y - x ≤ 1 / (2 : ℝ) ^ (r + 1)) :
    |FormalizacaoL55c.F f r y - FormalizacaoL55c.F f r x| ≤ Mseq p s CW S f r * (y - x) := by
  set N : ℕ := 2 ^ (r + 1) with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNe : ((N : ℕ) : ℝ) = (2 : ℝ) ^ (r + 1) := by rw [hNdef]; push_cast; ring
  have hd' : y - x ≤ 1 / (N : ℝ) := by rw [hNe]; exact hd
  have hLam : 0 ≤ Lam0 p CW f := by
    unfold Lam0; positivity
  have hKs : 0 ≤ Kslope p CW S := by
    unfold Kslope; positivity
  have hMnn : 0 ≤ Mseq p s CW S f r := Mseq_nonneg f S hLam hKs r
  -- nó `c = j/N` à esquerda de `y`, com `j = min ⌊yN⌋ (N-1)`
  set j0 : ℕ := ⌊y * N⌋₊ with hj0
  set j : ℕ := min j0 (N - 1) with hj
  have hjN : j < N := by omega
  have hjle : (j : ℝ) ≤ y * N := by
    have h1 : j ≤ j0 := min_le_left _ _
    have h2 : (j0 : ℝ) ≤ y * N := Nat.floor_le (mul_nonneg hy.1 hNr.le)
    have h3 : (j : ℝ) ≤ (j0 : ℝ) := by exact_mod_cast h1
    linarith
  have hyj : y * N ≤ (j : ℝ) + 1 := by
    rcases le_total j0 (N - 1) with h | h
    · have hjj : j = j0 := min_eq_left h
      have h1 : y * N < (j0 : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hjj]; linarith
    · have hjj : j = N - 1 := min_eq_right h
      have hyle : y ≤ 1 := hy.2
      have hN' : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
        have : N - 1 + 1 = N := by omega
        exact_mod_cast this
      rw [hjj, hN']
      nlinarith
  set c : ℝ := (j : ℝ) / N with hc
  have hcy : c ≤ y := by
    rw [hc, div_le_iff₀ hNr]; linarith
  have hyc : y ≤ ((j : ℝ) + 1) / N := by
    rw [le_div_iff₀ hNr]; linarith
  have hcell_eq : ∀ i : ℕ, cell N i = Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
    intro i
    unfold cell tn
    push_cast
    rfl
  have hcell_j : ∀ i : ℕ, i < N → ∀ u ∈ cell N i, ∀ w ∈ cell N i,
      |FormalizacaoL55c.F f r u - FormalizacaoL55c.F f r w| ≤ Mseq p s CW S f r * |u - w| :=
    fun i hi u hu w hw => cell_lip hp hW hCW hf hfi hfin hS hbS hs r (by rw [hNdef] at hi; exact hi) hu hw
  rcases le_or_gt c x with hcx | hcx
  · -- caso A: `x, y ∈ I_j`
    have hu : x ∈ cell N j := by
      rw [hcell_eq]; exact ⟨hcx, le_trans hxy hyc⟩
    have hw : y ∈ cell N j := by
      rw [hcell_eq]; exact ⟨le_trans hcx hxy, hyc⟩
    have := hcell_j j hjN y hw x hu
    have hmm : |y - x| = y - x := abs_of_nonneg (by linarith)
    rw [hmm] at this
    exact this
  · -- caso B: `x < c`, logo `c > 0`, `j ≥ 1`, e `x, c ∈ I_{j-1}`, `y, c ∈ I_j`
    have hcpos : 0 < c := lt_of_le_of_lt hx.1 hcx
    have hj1 : 1 ≤ j := by
      by_contra h
      have hj0' : j = 0 := by omega
      have : c = 0 := by rw [hc, hj0']; simp
      linarith
    have hjcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub hj1]; simp
    have hjN1 : j - 1 < N := by omega
    have hcellJ1 : cell N (j - 1) = Icc (((j : ℝ) - 1) / N) ((j : ℝ) / N) := by
      rw [hcell_eq, hjcast]
      have e1 : ((j : ℝ) - 1 + 1) = j := by ring
      rw [e1]
    have hdiv1 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    have hyJ : y ∈ cell N j := by
      rw [hcell_eq]; exact ⟨hcy, hyc⟩
    have hcJ : c ∈ cell N j := by
      rw [hcell_eq]
      exact ⟨le_refl _, div_le_div_of_nonneg_right (by linarith) hNr.le⟩
    have hcJ1 : c ∈ cell N (j - 1) := by
      rw [hcellJ1]
      exact ⟨by rw [hc, sub_div]; linarith, le_refl _⟩
    have hxJ1 : x ∈ cell N (j - 1) := by
      rw [hcellJ1]
      refine ⟨?_, hcx.le⟩
      have h1 : (j : ℝ) / N - 1 / N = ((j : ℝ) - 1) / N := by rw [sub_div]
      linarith
    have e1 := hcell_j j hjN y hyJ c hcJ
    have e2 := hcell_j (j - 1) hjN1 c hcJ1 x hxJ1
    have hsplit : FormalizacaoL55c.F f r y - FormalizacaoL55c.F f r x =
        (FormalizacaoL55c.F f r y - FormalizacaoL55c.F f r c) +
          (FormalizacaoL55c.F f r c - FormalizacaoL55c.F f r x) := by ring
    have hyc' : 0 ≤ y - c := by linarith
    have hcx' : 0 ≤ c - x := by linarith
    have a1 : |y - c| = y - c := abs_of_nonneg hyc'
    have a2 : |c - x| = c - x := abs_of_nonneg hcx'
    rw [a1] at e1
    rw [a2] at e2
    rw [hsplit]
    calc |(FormalizacaoL55c.F f r y - FormalizacaoL55c.F f r c) +
          (FormalizacaoL55c.F f r c - FormalizacaoL55c.F f r x)|
        ≤ |FormalizacaoL55c.F f r y - FormalizacaoL55c.F f r c| +
          |FormalizacaoL55c.F f r c - FormalizacaoL55c.F f r x| := abs_add_le _ _
      _ ≤ Mseq p s CW S f r * (y - c) + Mseq p s CW S f r * (c - x) := add_le_add e1 e2
      _ = Mseq p s CW S f r * (y - x) := by ring

end FormalizacaoL55d
