import Formalizacao.ModuloENN
import Pendencias.Realizacao

/-!
# Instância do arcabouço abstrato em `L^∞` (marco M1, refatoração da Parte IV)

O módulo da Parte IV, `ω₂(f,t)_{∞,[0,1]}` (`Pendencias.Agenda.omega2`), com a norma uniforme
`‖f‖_{∞,[0,1]} = distInf f 0`, satisfaz os três axiomas de `ModuloE`. Logo a desigualdade inversa
e a inclusão `R ⊆ B` em `L^∞` são casos dos teoremas abstratos `inverse_E` e
`stratum_subset_besovE`. Prova-se a conexão com as definições da Parte IV (`realG`, `RGQ`,
`RGInf`, `BesovQ`, `BesovInf`) e reobtêm-se, a partir do arcabouço, os resultados análogos.
-/

open scoped ENNReal
open Set Pendencias.Agenda Pendencias.Jackson Formalizacao.ModE

namespace FormalizacaoInf

/-- norma uniforme em `[0,1]`, em `[0,∞]` -/
noncomputable def nInf (f : ℝ → ℝ) : ℝ≥0∞ := distInf f 0

lemma nInf_sub (f g : ℝ → ℝ) : nInf (f - g) = distInf f g := by
  unfold nInf distInf
  simp [Pi.sub_apply]

/-- subaditividade do segundo módulo uniforme -/
lemma omega2_add_le (f g : ℝ → ℝ) (t : ℝ) : omega2 (f + g) t ≤ omega2 f t + omega2 g t := by
  unfold omega2
  refine iSup_le fun h => iSup_le fun hh => iSup_le fun x => iSup_le fun hx => ?_
  have e : |(f + g) (x + 2 * h) - 2 * (f + g) (x + h) + (f + g) x| ≤
      |f (x + 2 * h) - 2 * f (x + h) + f x| + |g (x + 2 * h) - 2 * g (x + h) + g x| := by
    simp only [Pi.add_apply]
    calc _ = |(f (x + 2 * h) - 2 * f (x + h) + f x) + (g (x + 2 * h) - 2 * g (x + h) + g x)| := by
          ring_nf
      _ ≤ _ := abs_add_le _ _
  calc ENNReal.ofReal |(f + g) (x + 2 * h) - 2 * (f + g) (x + h) + (f + g) x|
      ≤ ENNReal.ofReal (|f (x + 2 * h) - 2 * f (x + h) + f x| +
          |g (x + 2 * h) - 2 * g (x + h) + g x|) := ENNReal.ofReal_le_ofReal e
    _ = ENNReal.ofReal |f (x + 2 * h) - 2 * f (x + h) + f x| +
          ENNReal.ofReal |g (x + 2 * h) - 2 * g (x + h) + g x| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ omega2 f t + omega2 g t := add_le_add (le_omega2 hh hx) (le_omega2 hh hx)

/-- **A instância:** `ω = ω₂` e `nrm = ‖·‖_{∞,[0,1]}` satisfazem os axiomas. -/
noncomputable def modInf : ModuloE nInf where
  ω := fun f t => omega2 f t
  subadd := fun f g t => omega2_add_le f g t
  bound := fun g t => omega2_le_norm g t
  mono := fun f s t h => omega2_mono_t f h

lemma realE_modInf (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) (f : ℝ → ℝ) :
    realE modInf G N f = realG G N f := by
  unfold realE realG
  refine iInf_congr fun g => iInf_congr fun _ => ?_
  rw [nInf_sub]; rfl

/-- **Desigualdade inversa em `L^∞`, obtida do arcabouço** (resultado análogo a `inverse_realG`). -/
theorem inverse_realG_of_abstract (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) (f : ℝ → ℝ) :
    omega2 f (1 / N) ≤ 4 * realG G N f := by
  rw [← realE_modInf]
  exact inverse_E modInf G N f

lemma rpow_two_pow (r : ℕ) (s : ℝ) : ((2 : ℝ) ^ r) ^ s = (2 : ℝ) ^ ((r : ℝ) * s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- o termo de Besov abstrato é o `bterm` da Parte IV -/
lemma bterm_eq (s : ℝ) (f : ℝ → ℝ) (r : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) * modInf.ω f (1 / (2 : ℝ) ^ r) = bterm s f r := by
  unfold bterm modInf
  simp only
  rw [one_div, rpow_two_pow]

/-- `B^s_{∞,∞}` abstrato é o `BesovInf` da Parte IV -/
theorem besovE_top_iff (s : ℝ) (f : ℝ → ℝ) : f ∈ besovE modInf s ⊤ ↔ BesovInf s f := by
  have key : (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) * modInf.ω f (1 / (2 : ℝ) ^ r))
      = fun r => bterm s f r := funext fun r => bterm_eq s f r
  have hlq : lqE ⊤ (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
      modInf.ω f (1 / (2 : ℝ) ^ r)) = ⨆ r : ℕ, bterm s f r := by
    rw [key]; unfold lqE; rw [if_pos rfl]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hlq] at h2
    exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  · intro h
    refine ⟨(ENNReal.add_lt_top.1 h).1, ?_⟩
    rw [hlq]
    exact (ENNReal.add_lt_top.1 h).2

/-- `B^s_{∞,q}` abstrato (`0 < q < ∞`) é o `BesovQ` da Parte IV -/
theorem besovE_fin_iff {q : ℝ} (hq : 0 < q) (s : ℝ) (f : ℝ → ℝ) :
    f ∈ besovE modInf s (ENNReal.ofReal q) ↔ BesovQ s q f := by
  have hne : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq.le
  have key : (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) * modInf.ω f (1 / (2 : ℝ) ^ r))
      = fun r => bterm s f r := funext fun r => bterm_eq s f r
  have hlq : lqE (ENNReal.ofReal q) (fun r : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((r : ℝ) * s)) *
      modInf.ω f (1 / (2 : ℝ) ^ r)) = (∑' r : ℕ, bterm s f r ^ q) ^ (1 / q) := by
    rw [key]; unfold lqE; rw [if_neg hne, hqr, one_div]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hlq] at h2
    exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  · intro h
    refine ⟨(ENNReal.add_lt_top.1 h).1, ?_⟩
    rw [hlq]
    exact (ENNReal.add_lt_top.1 h).2

/-- o termo do estrato abstrato é o `rG` da Parte IV -/
lemma rG_eq (s : ℝ) (G : ℕ → Set (ℝ → ℝ)) (f : ℝ → ℝ) (r : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) * s)) * realE modInf G (2 ^ (r + 1)) f =
      rG s G f (r + 1) := by
  unfold rG
  rw [realE_modInf, ← rpow_two_pow]

/-- **Inclusão `R^s_q(G) ⊆ B^s_{∞,q}` em `L^∞`, obtida do arcabouço**
(resultado análogo a `besov_of_RGQ`, para `BesovQ`). -/
theorem besovQ_of_RGQ_abstract {s q : ℝ} (hq : 0 < q) {G : ℕ → Set (ℝ → ℝ)} {f : ℝ → ℝ}
    (hf : f ∈ RGQ s q G) : BesovQ s q f := by
  obtain ⟨hfc, hfin⟩ := hf
  have hne : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq.le
  have hstr : f ∈ stratumE modInf G s (ENNReal.ofReal q) := by
    refine ⟨distInf_lt_top_of_cont hfc, ?_⟩
    simp only [lqE, if_neg hne, hqr, rG_eq]
    rw [one_div] at hfin
    exact hfin
  exact (besovE_fin_iff hq s f).1
    (stratum_subset_besovE modInf G s _ (ENNReal.ofReal_pos.2 hq) hstr)

/-- idem para `q = ∞` -/
theorem besovInf_of_RGInf_abstract {s : ℝ} {G : ℕ → Set (ℝ → ℝ)} {f : ℝ → ℝ}
    (hf : f ∈ RGInf s G) : BesovInf s f := by
  obtain ⟨hfc, hfin⟩ := hf
  have hstr : f ∈ stratumE modInf G s ⊤ := by
    refine ⟨distInf_lt_top_of_cont hfc, ?_⟩
    simp only [lqE, rG_eq]
    exact hfin
  exact (besovE_top_iff s f).1 (stratum_subset_besovE modInf G s _ ENNReal.zero_lt_top hstr)

end FormalizacaoInf
