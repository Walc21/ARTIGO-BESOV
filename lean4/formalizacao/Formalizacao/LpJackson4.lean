import Formalizacao.LpJackson3

/-!
# M8, parte 4: `J_p` com as constantes do artigo

`HypJpStrong p s`: existem `C₀` e `C₁` (escolhidos **antes** de `f`) tais que, para toda `f`
mensurável e contínua em `[0,1]` em `B^s_{p,∞}`, existe `n₀(f)` e, para toda potência de dois
`n = 2^r ≥ n₀` e todo `H ≥ max{8 n^{ν_s}, 32(R+1)}`, `R = ‖f‖_∞`, um `g ∈ A_{n,H}` com
`‖f - g‖_p ≤ C₀ ω_p(f,1/n) + C₁ (R+1)/H`. É o enunciado do artigo (`lp:hyp:jackson`), com
`C₀ = C₀(p)` e `C₁` absoluto. A demonstração dá `C₀ = 9 C_W(p)` e `C₁ = 16`.
-/

open scoped ENNReal
open MeasureTheory Set FormalizacaoGrid FormalizacaoLp Artigo

namespace FormalizacaoJ

/-- `J_p` com as constantes do artigo -/
def HypJpStrong (p : ℝ≥0∞) (s : ℝ) : Prop :=
  ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ f : ℝ → ℝ, Measurable f → ContinuousOn f (Icc 0 1) →
    f ∈ besovP p s ⊤ → ∃ n0 : ℕ, ∀ r : ℕ, 2 ^ r ≥ n0 → ∀ H : ℕ,
      (H : ℝ) ≥ max (8 * ((2 : ℝ) ^ r) ^ (max 1 s))
        (32 * ((⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal + 1)) →
      ∃ g ∈ classNH (2 ^ r) H, eLpNorm (f - g) p vol01 ≤
        ENNReal.ofReal C0 * wtP p (1 / (2 : ℝ) ^ r) f +
          ENNReal.ofReal C1 *
            ENNReal.ofReal ((⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal + 1) / (H : ℝ≥0∞)

/-- **O teorema de Jackson racional em `L^p`, com as constantes do artigo.** -/
theorem hypJpStrong_of_lt {p s : ℝ} (hp : 1 ≤ p) (_hs : 1 / p < s) :
    HypJpStrong (ENNReal.ofReal p) s := by
  obtain ⟨CW, hCW, hq⟩ := FormalizacaoW.quasi_error_unc hp
  refine ⟨9 * CW, 16, by positivity, by norm_num, ?_⟩
  intro f hf hfc hbes
  obtain ⟨hfin', _⟩ := hbes
  have hfin : Np p f (Icc 0 1) < ⊤ := hfin'
  have hfi : IntegrableOn f (Icc 0 1) := hfc.integrableOn_Icc
  -- `R = ‖f‖_∞` e a cota pontual
  have hdist : (⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|) = Pendencias.Agenda.distInf f 0 := by
    unfold Pendencias.Agenda.distInf; simp
  have hRfin : (⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|) ≠ ⊤ := by
    rw [hdist]; exact (Pendencias.Jackson.distInf_lt_top_of_cont hfc).ne
  set R : ℝ := (⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x|).toReal with hRdef
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hfR : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ R := by
    intro x hx
    have h1 : ENNReal.ofReal |f x| ≤ ⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x| :=
      le_iSup₂ (f := fun x (_ : x ∈ Icc (0 : ℝ) 1) => ENNReal.ofReal |f x|) x hx
    exact (ENNReal.ofReal_le_iff_le_toReal hRfin).1 h1
  have hlam : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, j ≤ n → |lam n f j| ≤ 2 * R := fun n hn j hj =>
    abs_lam_sup_le hn hR0 j hj (fun y hy => hfR y (cell_sub_unit (by unfold cellIdx; omega) hy))
  obtain ⟨_, _, _, hsmall⟩ := nodal_G hfc
  obtain ⟨n1, hn1⟩ := hsmall 1 one_pos
  refine ⟨max n1 2, ?_⟩
  intro r hr H hH
  set n : ℕ := 2 ^ r with hn
  have hr' : max n1 2 ≤ n := hr
  have hn1le : n1 ≤ n := (max_le_iff.1 hr').1
  have hn2 : 2 ≤ n := (max_le_iff.1 hr').2
  have hn1' : 1 ≤ n := by omega
  have hHn : 8 * (2 : ℝ) ^ r ≤ H := by
    have h1 : 8 * ((2 : ℝ) ^ r) ^ (max 1 s) ≤ H := (le_max_left _ _).trans hH
    have h2 : (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ (max 1 s) :=
      Real.self_le_rpow_of_one_le (one_le_pow₀ (by norm_num)) (le_max_left 1 s)
    linarith
  have hH32 : 32 * (R + 1) ≤ (H : ℝ) := (le_max_right _ _).trans hH
  have hH16 : 16 * (2 * R + 1) ≤ (H : ℝ) := by linarith
  have hHpos : (0 : ℝ) < H := by
    have : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨g, hg, hbound⟩ := lp_jackson_core hp hq hf hfi hfin hR0 hn2
    (fun j hj => hlam n hn1' j hj) (fun j hj => hn1 n hn1le hn2 j hj) hHn hH16
  refine ⟨g, hg, hbound.trans ?_⟩
  have hCa : ENNReal.ofReal (9 * CW) = 9 * ENNReal.ofReal CW := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have hH' : ENNReal.ofReal (8 * (2 * R + 1) / H) ≤
      ENNReal.ofReal 16 * ENNReal.ofReal (R + 1) / (H : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos hHpos, ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal ?_) _
    linarith
  rw [hCa]
  exact add_le_add le_rfl hH'

/-- **Observação de imersão** (`lp:rem:embedding-fact`): para `1/p < s`, todo elemento mensurável de
`B^s_{p,∞}` coincide quase sempre com uma função contínua em `[0,1]`. A hipótese de continuidade em
`HypJpStrong` não restringe, portanto, a classe. -/
theorem besov_continuous_rep {p s : ℝ} (hp : 1 ≤ p) (hs : 1 / p < s) {f : ℝ → ℝ}
    (hf : Measurable f) (hbes : f ∈ besovP (ENNReal.ofReal p) s ⊤) :
    ∃ G : ℝ → ℝ, ContinuousOn G (Icc 0 1) ∧
      ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), f x = G x := by
  obtain ⟨hfin', hlq⟩ := hbes
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hfin : Np p f (Icc 0 1) < ⊤ := hfin'
  have hfi : IntegrableOn f (Icc 0 1) := by
    have hmem : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc (0 : ℝ) 1)) :=
      ⟨hf.aestronglyMeasurable, hfin'⟩
    exact hmem.integrable hp1
  set S := lqNorm ⊤ (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
    wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f) with hSdef
  have hS : S < ⊤ := hlq
  have hbS : ∀ m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ m) f ≤ S := by
    intro m
    rw [hSdef, lqNorm, if_pos rfl]
    exact le_iSup (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
      wtP (ENNReal.ofReal p) (1 / (2 : ℝ) ^ r) f) m
  exact ⟨FormalizacaoL55c.Glim f, FormalizacaoW.Glim_continuousOn_unc hp hf hfi hfin hS hbS hs,
    FormalizacaoW.ae_eq_Glim_unc hp hf hfi hfin hS hbS hs⟩

end FormalizacaoJ
