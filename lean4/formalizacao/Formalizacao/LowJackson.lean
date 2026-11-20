import Formalizacao.LpJackson2
import Formalizacao.LowNodal

/-!
# Regimes `s ≤ 1/p`, parte 2: núcleo do Jackson sem continuidade

`lp_jackson_low_core` é o `Teorema lp:thm:jackson-low` do artigo, na forma em que as cotas
nodais são hipóteses: dado `M` com `|λ_j(f)| ≤ M` (`0 ≤ j ≤ 2^r`), `Q = 2^e ≥ 2^r` e
`H ≥ 8(M+1)Q`, existe `g ∈ A_{2^r,H}` com `‖f - g‖_p ≤ 9 C_W ω_p(f,1/2^r) + 1/(2Q)`.
Não há hipótese de continuidade nem de salto.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoLp Artigo

namespace FormalizacaoJ

theorem lp_jackson_low_core {p : ℝ} (hp : 1 ≤ p) {CW : ℝ}
    (hq : ∀ n : ℕ, 2 ≤ n → ∀ f : ℝ → ℝ, Measurable f → IntegrableOn f (Icc 0 1) →
      Np p f (Icc 0 1) < ⊤ → Np p (fun x => f x - Q n f x) (Icc 0 1) ≤
        9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (n : ℝ)) f)
    {f : ℝ → ℝ} (hf : Measurable f) (hfi : IntegrableOn f (Icc 0 1))
    (hfin : Np p f (Icc 0 1) < ⊤) {M : ℝ} (hM : 0 ≤ M) {r e : ℕ} (hr2 : 2 ≤ 2 ^ r)
    (hre : r ≤ e) (hlam : ∀ j : ℕ, j ≤ 2 ^ r → |lam (2 ^ r) f j| ≤ M)
    {H : ℕ} (hH : 8 * (M + 1) * 2 ^ e ≤ (H : ℝ)) :
    ∃ g ∈ classNH (2 ^ r) H, eLpNorm (f - g) (ENNReal.ofReal p) vol01 ≤
      9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f +
        ENNReal.ofReal (1 / (2 * 2 ^ e)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  set n : ℕ := 2 ^ r with hn
  have hnR2 : ((2 : ℝ) ^ r) = (n : ℝ) := by rw [hn]; push_cast; ring
  have hn1' : 1 ≤ n := by omega
  set y : ℤ → ℝ := fun m => lam n f m.toNat with hy
  have hyb : ∀ m : ℤ, 0 ≤ m → m ≤ 2 ^ r → |y m| ≤ M := by
    intro m h0 h1
    simp only [hy]
    refine hlam m.toNat ?_
    have : m ≤ (n : ℤ) := by rw [hn]; push_cast; exact h1
    omega
  obtain ⟨T, hT, hbound⟩ := nodal_tree_gen hre hM (y := y) hyb hH
  refine ⟨T.eval 0 0, ⟨T, (Pendencias.Jackson.admK_zero _ _ _).1 hT, rfl⟩, ?_⟩
  set g : ℝ → ℝ := T.eval 0 0 with hg
  have hgm : Measurable g := measurable_eval T 0 0
  have hQc : Continuous (Q n f) := FormalizacaoL55.Q_continuous n f
  have hnode : ∀ m : ℤ, 0 ≤ m → m ≤ 2 ^ r → Q n f (cL r m) = y m := by
    intro m h0 h1
    have hk : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0
    have hcL : cL r m = tn n m.toNat := by
      unfold cL tn; rw [hk, hnR2]
    rw [hcL]
    have : m.toNat ≤ n := by
      have : m ≤ (n : ℤ) := by rw [hn]; push_cast; exact h1
      omega
    exact Q_node hn1' f this
  have hcell : ∀ m : ℤ, 0 ≤ m → m < 2 ^ r → ∃ α β : ℝ, ∀ x ∈ cellIcc r m, Q n f x = α + β * x := by
    intro m h0 h1
    have hk : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0
    have hlt : m.toNat < n := by
      have : m < (n : ℤ) := by rw [hn]; push_cast; exact h1
      omega
    obtain ⟨α, β, h⟩ := FormalizacaoL55.Q_affine_on_cell hn1' hlt f
    refine ⟨α, β, fun x hx => h x ?_⟩
    have hx' : x ∈ Icc ((m : ℝ) / 2 ^ r) (((m : ℝ) + 1) / 2 ^ r) := hx
    unfold cell tn
    push_cast
    rw [hk]
    rw [hnR2] at hx'
    exact hx'
  have hbd := hbound (Q n f) hnode hcell
  have hbd2 : eLpNorm (fun x => Q n f x - g x) (ENNReal.ofReal p) vol01 ≤
      ENNReal.ofReal (1 / (2 * 2 ^ e)) := by
    have hae : ∀ᵐ x ∂vol01, ‖Q n f x - g x‖ ≤ 1 / (2 * 2 ^ e) := by
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_)
      have hx' : x ∈ cellIcc 0 0 := by simpa [cellIcc] using hx
      rw [Real.norm_eq_abs]; exact hbd x hx'
    calc eLpNorm (fun x => Q n f x - g x) (ENNReal.ofReal p) vol01
        ≤ vol01 Set.univ ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal (1 / (2 * 2 ^ e)) :=
          eLpNorm_le_of_ae_bound hae
      _ = ENNReal.ofReal (1 / (2 * 2 ^ e)) := by
          have : vol01 Set.univ = 1 := by
            simp [vol01, Real.volume_Icc]
          rw [this, ENNReal.one_rpow, one_mul]
  have hbd1 : eLpNorm (fun x => f x - Q n f x) (ENNReal.ofReal p) vol01 ≤
      9 * ENNReal.ofReal CW * wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f := by
    have := hq n hr2 f hf hfi hfin
    rw [hnR2]
    exact this
  have hsum : eLpNorm (f - g) (ENNReal.ofReal p) vol01 ≤
      eLpNorm (fun x => f x - Q n f x) (ENNReal.ofReal p) vol01 +
        eLpNorm (fun x => Q n f x - g x) (ENNReal.ofReal p) vol01 := by
    have e' : f - g = (fun x => f x - Q n f x) + (fun x => Q n f x - g x) := by
      funext x; simp
    rw [e']
    exact eLpNorm_add_le (hf.sub hQc.measurable).aestronglyMeasurable
      (hQc.measurable.sub hgm).aestronglyMeasurable hp1
  exact hsum.trans (add_le_add hbd1 hbd2)

end FormalizacaoJ
