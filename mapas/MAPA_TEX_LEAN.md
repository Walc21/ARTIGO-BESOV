# Correspondência do artigo sobre $L^p$ com Lean 4

Gerado por `mapas/gerar_mapa.py` a partir de `mapas/dados/mapa_lp.json`. O verificador confere os rótulos do TeX, localiza as declarações nos arquivos indicados e valida os nomes com `#check`. O apêndice A descreve a relação entre os enunciados do artigo e a formalização.

O projeto usa Lean 4.28.0 e Mathlib v4.28.0. A auditoria de dependências axiomáticas está em `lean4/formalizacao/Formalizacao/Auditoria.lean`, com saída registrada em `lean4/formalizacao/auditoria_axiomas.txt`.

## Correspondências

### D1 — módulo de suavidade $\omega_p$ e convenção

Texto: [conjecturas_lp.tex:145](../conjecturas_lp.tex); rótulo `lp:eq:modulus-p`.

Estado: **Formalizado (definição)**. Convenção da Parte IV: a segunda diferença usa $x, x+h, x+2h \in [0,1]$ e o supremo é sobre $0<h\le\min\{t,1/2\}$. A norma é `eLpNorm` na medida de Lebesgue restrita a `[0, 1-2h]`.

- [`FormalizacaoLp.diff2`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 26.
- [`FormalizacaoLp.wtP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 30.
- [`FormalizacaoLp.vol01`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 23.

### D2 — espaço de Besov diádico $B^s_{p,q}$

Texto: [conjecturas_lp.tex:157](../conjecturas_lp.tex); rótulo `lp:eq:besov-p`.

Estado: **Formalizado (definição)**. `besovP p s q` exige `f ∈ L^p` e a sequência `(2^{rs} ω_p(f, 2^{-r}))_{r≥0}` em `ℓ^q`; a norma `ℓ^q` é `lqNorm` (`q = ∞` é o supremo).

- [`FormalizacaoLp.lqNorm`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 44.
- [`FormalizacaoLp.besovP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 57.

### D3 — biblioteca $\Sigma_N$ e agendas $H_{s,\kappa}$, $\widetilde H_{s,\eta}$

Texto: [conjecturas_lp.tex:181](../conjecturas_lp.tex); rótulo `lp:eq:schedule`.

Estado: **Formalizado (definição)**. A biblioteca da Parte IV é representada por `Sigma H N = {0} ∪ 𝒜_{N,H(N)}`. As agendas são `Hsk s κ` e `HtilK 0 0 s η`, com `CK 0 0 = 8`. A classe `classNH N H` representa 𝒜_{N,H}.

- [`Pendencias.Agenda.Sigma`](../lean4/formalizacao/Pendencias/Agenda.lean) — linha 24.
- [`Pendencias.Agenda.Hsk`](../lean4/formalizacao/Pendencias/Inversa.lean) — linha 455.
- [`Pendencias.Jackson.HtilK`](../lean4/formalizacao/Pendencias/Direta.lean) — linha 292.
- [`Artigo.AdmNH`](../lean4/formalizacao/RequestProject/JointBudget.lean) — linha 27.
- [`Artigo.LTree`](../lean4/formalizacao/RequestProject/Trees.lean) — linha 61.
- [`FormalizacaoLp.classNH`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 64.

### D4 — mensurabilidade dos elementos de $\Sigma_N$

Texto: [conjecturas_lp.tex:175](../conjecturas_lp.tex); rótulo `lp:eq:sigma`.

Estado: **Formalizado e compilado**. A avaliação de uma árvore é mensurável por indução, pois a avaliação é definida por casos sobre folhas afins.

- [`FormalizacaoLp.measurable_eval`](../lean4/formalizacao/Formalizacao/Library.lean) — linha 17.
- [`FormalizacaoLp.measurable_sigma`](../lean4/formalizacao/Formalizacao/Library.lean) — linha 34.
- [`FormalizacaoLp.classNH_subset_sigma`](../lean4/formalizacao/Formalizacao/Library.lean) — linha 42.

### 2.1 — funcional e espaço de realização em $L^p$

Texto: [conjecturas_lp.tex:198](../conjecturas_lp.tex); rótulo `lp:def:realization`.

Estado: **Formalizado (definição)**. Em `ℝ≥0∞`. O estrato inclui a condição `f ∈ L^p`, como na definição do texto, e é reindexado por `r ↦ r+1` (começa em `N = 2`).

- [`FormalizacaoLp.distP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 35.
- [`FormalizacaoLp.realP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 40.
- [`FormalizacaoLp.stratumP`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 50.

### 2.2 — famílias aninhadas que contêm a biblioteca

Texto: [conjecturas_lp.tex:215](../conjecturas_lp.tex); rótulo `lp:def:network-family`.

Estado: **Formalizado (definição)**. As hipóteses de `Conj2Stability` expressam aninhamento, inclusão da função nula e inclusão da biblioteca após reescalonamento do orçamento. A declaração se aplica a famílias mensuráveis, entre elas as famílias de funções contínuas do artigo.

- [`FormalizacaoLp.Conj2Stability`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 89.
- [`FormalizacaoStab.fam_mono`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 26.

### 3.1 — caracterização de Besov por realização aritmética

Texto: [conjecturas_lp.tex:232](../conjecturas_lp.tex); rótulo `lp:conj:besov`.

Estado: **Formalizado e compilado**. Os itens (i), (ii) e (iii) estão formalizados. `conj1_low` e `conj1_diag` usam `p` real com `ENNReal.ofReal p`; as agendas são `Hsk (1 + 1/p - s) 0` e `Hsk 1 (thetaQ q + κ)`, que coincidem com $\widehat H_s$ e $\widehat H_{q,\kappa}$ do texto. O Lean não exige $s>0$ em (ii).

- [`FormalizacaoLp.Conj1Endpoint`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 71.
- [`FormalizacaoLp.Conj1Subcritical`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 76.
- [`FormalizacaoLp.Conj1Critical`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 81.
- [`FormalizacaoJ.conj1_endpoint`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 28.
- [`FormalizacaoJ.conj1_subcritical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 33.
- [`FormalizacaoJ.conj1_critical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 39.
- [`FormalizacaoJ.conj1_tilde`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 46.
- [`FormalizacaoLow.conj1_low`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 88.
- [`FormalizacaoLow.conj1_diag`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 99.

### 3.2 — estabilidade por inclusão de redes

Texto: [conjecturas_lp.tex:265](../conjecturas_lp.tex); rótulo `lp:conj:stability`.

Estado: **Formalizado e compilado**. As quatro declarações dão a estabilidade por inclusão para as agendas e os regimes do item (i) do Teorema 3.1 ($1/p<s<2$), com constante real $c\ge1$. O caso $s\le1/p$ não está formalizado. Para $s\le1/p$: `conj2_low` e `conj2_diag`.

- [`FormalizacaoLp.Conj2Stability`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 89.
- [`FormalizacaoJ.conj2_endpoint`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 54.
- [`FormalizacaoJ.conj2_subcritical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 59.
- [`FormalizacaoJ.conj2_critical`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 65.
- [`FormalizacaoJ.conj2_tilde`](../lean4/formalizacao/Formalizacao/LpJackson3.lean) — linha 72.
- [`FormalizacaoLow.conj2_low`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 44.
- [`FormalizacaoLow.conj2_diag`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 57.

### 4.1 — estimativa de Jackson em $L^p$

Texto: [conjecturas_lp.tex:286](../conjecturas_lp.tex); rótulo `lp:hyp:jackson`.

Estado: **Formalizado e compilado**. `hypJpStrong_of_lt` dá a estimativa com $C_0=9C_W(p)$ e $C_1=16$ para o representante contínuo. A forma usada nas reduções é demonstrada em `hypJp_of_lt` e permite constantes dependentes de $f$.

- [`FormalizacaoLp.HypJp`](../lean4/formalizacao/Formalizacao/LpDefs.lean) — linha 103.
- [`FormalizacaoJ.hypJp_of_lt`](../lean4/formalizacao/Formalizacao/LpJackson2.lean) — linha 152.
- [`FormalizacaoJ.hypJpStrong_of_lt`](../lean4/formalizacao/Formalizacao/LpJackson4.lean) — linha 30.
- [`FormalizacaoJ.lp_jackson_core`](../lean4/formalizacao/Formalizacao/LpJackson2.lean) — linha 25.

### 4.2 — projeção afim local

Texto: [conjecturas_lp.tex:311](../conjecturas_lp.tex); rótulo `lp:lem:projection`.

Estado: **Formalizado e compilado**. O núcleo reproduz funções afins, é simétrico e tem imagem afim. Os núcleos avaliam a projeção nos extremos, com cotas dadas por Hölder e pela integral do módulo de cada núcleo.

- [`FormalizacaoQuasi.abs_kL_le`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 33.
- [`FormalizacaoQuasi.abs_kR_le`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 45.
- [`FormalizacaoQuasi.integral_kL_mul_affine`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 58.
- [`FormalizacaoQuasi.integral_kR_mul_affine`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 98.
- [`FormalizacaoQuasi.abs_integral_kernel_le`](../lean4/formalizacao/Formalizacao/QuasiLocal.lean) — linha 138.
- [`FormalizacaoKer.kernel_is_affine_projection`](../lean4/formalizacao/Formalizacao/Kernel.lean) — linha 111.
- [`FormalizacaoKer.kL_eq_Kf`](../lean4/formalizacao/Formalizacao/Kernel.lean) — linha 27.
- [`FormalizacaoKer.kR_eq_Kf`](../lean4/formalizacao/Formalizacao/Kernel.lean) — linha 33.

### 4.3 — quase-interpolante

Texto: [conjecturas_lp.tex:333](../conjecturas_lp.tex); rótulo `lp:lem:quasi`.

Estado: **Formalizado e compilado**. Construção de $Q_n$, reprodução de funções afins, erro local e cotas de amplitude e de diferenças nodais.

- [`FormalizacaoGrid.Q_affine`](../lean4/formalizacao/Formalizacao/QuasiGrid.lean) — linha 183.
- [`FormalizacaoGrid.Q_cell`](../lean4/formalizacao/Formalizacao/QuasiGrid.lean) — linha 166.
- [`FormalizacaoGrid.abs_lam_sup_le`](../lean4/formalizacao/Formalizacao/QuasiGrid.lean) — linha 244.
- [`FormalizacaoGrid.local_error`](../lean4/formalizacao/Formalizacao/LocalError.lean) — linha 177.
- [`FormalizacaoL52d.lam_diff_le`](../lean4/formalizacao/Formalizacao/Lemma52d.lean) — linha 83.
- [`FormalizacaoL52d.omega1`](../lean4/formalizacao/Formalizacao/Lemma52d.lean) — linha 24.

### 4.4 — Whitney em partições de $L^p$

Texto: [conjecturas_lp.tex:360](../conjecturas_lp.tex); rótulo `lp:lem:whitney`.

Estado: **Formalizado e compilado**. A prova usa média dupla, fórmula de Taylor, reflexão, Jensen e Tonelli. A transferência das duas faixas extremas para o interior e a multiplicidade dos intervalos dão a estimativa global.

- [`FormalizacaoW.whitney_lp`](../lean4/formalizacao/Formalizacao/Whitney12.lean) — linha 31.
- [`FormalizacaoW.local_whitney`](../lean4/formalizacao/Formalizacao/Whitney7.lean) — linha 62.
- [`FormalizacaoW.taylor_lp`](../lean4/formalizacao/Formalizacao/Whitney2.lean) — linha 17.
- [`FormalizacaoW.double_sym`](../lean4/formalizacao/Formalizacao/Whitney3.lean) — linha 73.
- [`FormalizacaoW.fg_lp`](../lean4/formalizacao/Formalizacao/Whitney4.lean) — linha 140.
- [`FormalizacaoW.sum_lintegral_le`](../lean4/formalizacao/Formalizacao/Whitney8.lean) — linha 64.
- [`FormalizacaoW.Wt_global`](../lean4/formalizacao/Formalizacao/Whitney9.lean) — linha 15.
- [`FormalizacaoW.Ek_bound`](../lean4/formalizacao/Formalizacao/Whitney10.lean) — linha 77.
- [`FormalizacaoCor.WhitneyLp`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 32.

### 4.5 — erro de quase-interpolação

Texto: [conjecturas_lp.tex:427](../conjecturas_lp.tex); rótulo `lp:cor:quasi-error`.

Estado: **Formalizado e compilado**. `quasi_error_unc` deduz a cota global de `whitney_lp` e do erro local.

- [`FormalizacaoCor.quasi_error`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 124.
- [`FormalizacaoCor.local_error_inf`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 97.
- [`FormalizacaoCor.sum_cells_le`](../lean4/formalizacao/Formalizacao/Corollary54.lean) — linha 109.
- [`FormalizacaoW.quasi_error_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 18.

### 4.6 — imersão e cota de $\omega_1$

Texto: [conjecturas_lp.tex:442](../conjecturas_lp.tex); rótulo `lp:lem:embedding`.

Estado: **Formalizado e compilado**. A cota de Besov controla a série telescópica das diferenças de quase-interpolantes. A série fornece o representante contínuo e as estimativas do módulo de primeira ordem.

- [`FormalizacaoEmb.inverse_affine_sup`](../lean4/formalizacao/Formalizacao/Embedding.lean) — linha 90.
- [`FormalizacaoEmb.bernstein_affine`](../lean4/formalizacao/Formalizacao/Embedding.lean) — linha 100.
- [`FormalizacaoL55b.vk_sup_le`](../lean4/formalizacao/Formalizacao/Lemma55b.lean) — linha 108.
- [`FormalizacaoL55b.vk_slope_le`](../lean4/formalizacao/Formalizacao/Lemma55b.lean) — linha 159.
- [`FormalizacaoL55c.ae_eq_Glim`](../lean4/formalizacao/Formalizacao/Lemma55c.lean) — linha 284.
- [`FormalizacaoL55c.Glim_continuousOn`](../lean4/formalizacao/Formalizacao/Lemma55c.lean) — linha 215.
- [`FormalizacaoL55d.F_lip`](../lean4/formalizacao/Formalizacao/Lemma55d.lean) — linha 141.
- [`FormalizacaoL55e.modulus_lt1`](../lean4/formalizacao/Formalizacao/Lemma55e.lean) — linha 187.
- [`FormalizacaoL55e.modulus_eq1`](../lean4/formalizacao/Formalizacao/Lemma55e.lean) — linha 267.
- [`FormalizacaoL55e.modulus_gt1`](../lean4/formalizacao/Formalizacao/Lemma55e.lean) — linha 322.
- [`FormalizacaoW.Glim_continuousOn_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 27.
- [`FormalizacaoW.ae_eq_Glim_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 37.
- [`FormalizacaoW.modulus_lt1_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 47.
- [`FormalizacaoW.modulus_eq1_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 59.
- [`FormalizacaoW.modulus_gt1_unc`](../lean4/formalizacao/Formalizacao/Whitney13.lean) — linha 72.
- [`FormalizacaoJ.besov_continuous_rep`](../lean4/formalizacao/Formalizacao/LpJackson4.lean) — linha 87.

### 4.7 — interpolação racional com orçamento de altura

Texto: [conjecturas_lp.tex:484](../conjecturas_lp.tex); rótulo `lp:prop:jackson-proof`.

Estado: **Formalizado e compilado**. `nodal_tree` constrói o interpolante quantizado sob cotas de altura e de inclinação. A estimativa `lp_jackson_core` aplica essa construção aos valores nodais de $Q_n f$.

- [`FormalizacaoJ.nodal_tree`](../lean4/formalizacao/Formalizacao/LpJackson0.lean) — linha 18.
- [`FormalizacaoJ.Q_node`](../lean4/formalizacao/Formalizacao/LpJackson1.lean) — linha 16.
- [`FormalizacaoJ.lam_congr_ae`](../lean4/formalizacao/Formalizacao/LpJackson1.lean) — linha 38.
- [`FormalizacaoJ.nodal_G`](../lean4/formalizacao/Formalizacao/LpJackson1.lean) — linha 55.
- [`FormalizacaoJ.hypJp_of_lt`](../lean4/formalizacao/Formalizacao/LpJackson2.lean) — linha 152.

### 4.8 — interpolação racional sem controle dos saltos

Texto: [conjecturas_lp.tex:526](../conjecturas_lp.tex); rótulo `lp:lem:nodal-general`.

Estado: **Formalizado e compilado**. Árvore nodal com `Q = 2^e ≥ 2^r` e `H ≥ 8(M+1)Q`, sem hipótese sobre `|y_{n+1}-y_n|`; `lp_jackson_low_core` é o núcleo do Jackson para $s\le1/p$.

- [`FormalizacaoJ.nodal_tree_gen`](../lean4/formalizacao/Formalizacao/LowNodal.lean) — linha 19.
- [`FormalizacaoJ.lp_jackson_low_core`](../lean4/formalizacao/Formalizacao/LowJackson.lean) — linha 18.

### 4.9 — cota em sup dos quase-interpolantes

Texto: [conjecturas_lp.tex:535](../conjecturas_lp.tex); rótulo `lp:lem:sup-bound`.

Estado: **Formalizado e compilado**. Na forma «existe `K ≥ 1`, dependendo de `f`», com `Lam p s q r` $=\Lambda_r$. As somas parciais de $\ell^q$ estão em `sum_le_lq`.

- [`FormalizacaoLow.step_le`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 33.
- [`FormalizacaoLow.Q_sup_le`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 61.
- [`FormalizacaoLow.Lam`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 89.
- [`FormalizacaoLow.lam_bound`](../lean4/formalizacao/Formalizacao/LowSup.lean) — linha 114.
- [`FormalizacaoLow.thetaQ`](../lean4/formalizacao/Formalizacao/LowSum.lean) — linha 19.
- [`FormalizacaoLow.sum_le_lq`](../lean4/formalizacao/Formalizacao/LowSum.lean) — linha 53.

### 4.10 — Jackson para $s\le1/p$

Texto: [conjecturas_lp.tex:559](../conjecturas_lp.tex); rótulo `lp:thm:jackson-low`.

Estado: **Formalizado e compilado**. As constantes $C_W$ e $K$ dependem de `f`, em vez de $C_0(S+1)$ do texto.

- [`FormalizacaoLow.classNH_le_sigma`](../lean4/formalizacao/Formalizacao/LowJackson2.lean) — linha 19.
- [`FormalizacaoLow.jackson_low`](../lean4/formalizacao/Formalizacao/LowJackson2.lean) — linha 24.

### 5.1 — propriedades do módulo em $L^p$

Texto: [conjecturas_lp.tex:582](../conjecturas_lp.tex); rótulo `lp:lem:modulus`.

Estado: **Formalizado e compilado**. Para `1 ≤ p` e funções mensuráveis. `modC` mostra que são exatamente os três axiomas do arcabouço abstrato.

- [`FormalizacaoLp.wtP_add_le`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 42.
- [`FormalizacaoLp.wtP_le_four`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 152.
- [`FormalizacaoLp.wtP_mono_t`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 53.
- [`FormalizacaoLp.modC`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 33.
- [`Formalizacao.ModE.ModuloE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 21.

### 5.2 — desigualdade inversa em $L^p$

Texto: [conjecturas_lp.tex:596](../conjecturas_lp.tex); rótulo `lp:prop:inverse`.

Estado: **Formalizado e compilado**. A cota `ω_p(f,1/N) ≤ 4 R_N(f)` vale para toda família de funções mensuráveis; a segunda afirmação usa `0 ∈ G_N`. Também está provada no arcabouço abstrato, em valores reais e em `ℝ≥0∞`, e transferida à instância `L^p`.

- [`FormalizacaoLp.wtP_le_four_realP`](../lean4/formalizacao/Formalizacao/LpAxioms.lean) — linha 162.
- [`FormalizacaoRed.realP_le_norm`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 113.
- [`Formalizacao.ModE.inverse_E`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 52.
- [`Formalizacao.inverse_le`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 59.
- [`FormalizacaoLp.wtP_le_four_realP_of_abstract`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 75.

### 5.3 — inclusão $\mathscr R\subset B$

Texto: [conjecturas_lp.tex:616](../conjecturas_lp.tex); rótulo `lp:cor:inclusion`.

Estado: **Formalizado e compilado**. Vale para `0 < q ≤ ∞`, qualquer família de funções mensuráveis, sem relação com a agenda.

- [`FormalizacaoLp.stratum_subset_besov_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 84.
- [`Formalizacao.ModE.stratum_subset_besovE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 109.
- [`Formalizacao.ModE.lqE_lt_top_of_succ_le`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 70.
- [`Formalizacao.stratum_subset_besov`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 139.

### 5.4 — critério de somabilidade da agenda

Texto: [conjecturas_lp.tex:628](../conjecturas_lp.tex); rótulo `lp:thm:besov-conditional`.

Estado: **Formalizado e compilado, condicional a $J_p$**. `besov_subset_stratum` usa a estimativa de Jackson para a inclusão direta sob o critério de somabilidade. As quatro reduções especializam a agenda.

- [`FormalizacaoRed.besov_subset_stratum`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 137.
- [`FormalizacaoRed.realP_le_of_approx`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 41.
- [`FormalizacaoThm.conj1_endpoint_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 27.
- [`FormalizacaoThm.conj1_subcritical_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 44.
- [`FormalizacaoThm.conj1_critical_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 71.
- [`FormalizacaoThm.conj1_tilde_of_J`](../lean4/formalizacao/Formalizacao/Theorems.lean) — linha 90.
- [`FormalizacaoSched.weight_bdd`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 163.
- [`FormalizacaoSched.weight_geom`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 45.
- [`FormalizacaoSched.weight_poly`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 79.
- [`FormalizacaoSched.Hsk_low`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 132.
- [`FormalizacaoSched.Htil_low`](../lean4/formalizacao/Formalizacao/Schedules.lean) — linha 151.
- [`FormalizacaoLq.lq_of_eventually_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 128.
- [`FormalizacaoLq.lq_of_geom_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 168.
- [`FormalizacaoLq.lq_of_poly_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 200.

### 5.5 — transferência da estimativa direta para famílias aninhadas

Texto: [conjecturas_lp.tex:663](../conjecturas_lp.tex); rótulo `lp:thm:stability-conditional`.

Estado: **Formalizado e compilado, condicional a $J_p$**. O aproximante de Jackson na escala deslocada fornece a inclusão direta. A desigualdade inversa dá a igualdade nas declarações de estabilidade.

- [`FormalizacaoStab.besov_subset_stratum_fam`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 33.
- [`FormalizacaoStab.stability_iff_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 161.
- [`FormalizacaoStab.conj2Stability_endpoint_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 274.
- [`FormalizacaoStab.conj2Stability_subcritical_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 278.
- [`FormalizacaoStab.conj2Stability_critical_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 284.
- [`FormalizacaoStab.conj2Stability_tilde_of_J`](../lean4/formalizacao/Formalizacao/Stability.lean) — linha 291.
- [`FormalizacaoRed.realP_le_of_approx'`](../lean4/formalizacao/Formalizacao/Reductions.lean) — linha 86.
- [`FormalizacaoLq.lq_tail_le`](../lean4/formalizacao/Formalizacao/LqLemmas.lean) — linha 233.

### 5.6 — transferência para $s\le1/p$

Texto: [conjecturas_lp.tex:686](../conjecturas_lp.tex); rótulo `lp:thm:low-transfer`.

Estado: **Formalizado e compilado**. A condição de deslocamento do texto é `hshift`; o expoente extra `m` é `0` ($s<1/p$) ou `mDiag κ` ($s=1/p$).

- [`FormalizacaoLow.besov_subset_stratum_low`](../lean4/formalizacao/Formalizacao/LowTransfer.lean) — linha 21.
- [`FormalizacaoLow.hshift_low`](../lean4/formalizacao/Formalizacao/LowShift.lean) — linha 21.
- [`FormalizacaoLow.hshift_diag`](../lean4/formalizacao/Formalizacao/LowShift.lean) — linha 75.
- [`FormalizacaoLow.mDiag`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 65.
- [`FormalizacaoLow.mDiag_ge`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 72.
- [`FormalizacaoLow.mDiag_le`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 78.
- [`FormalizacaoLow.wreal_geom`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 45.
- [`FormalizacaoLow.wreal_poly`](../lean4/formalizacao/Formalizacao/LowWeights.lean) — linha 90.
- [`FormalizacaoLow.hW_geom`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 23.
- [`FormalizacaoLow.hW_poly`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 34.
- [`FormalizacaoLow.sigma_family`](../lean4/formalizacao/Formalizacao/LowTheorems.lean) — linha 77.

### F1 — arcabouço abstrato do módulo, em valores reais

Texto: [conjecturas_lp.tex:722](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. Estrutura `ModuloAbs` sobre um espaço seminormado; `ω` real. Serve de modelo para a versão em `ℝ≥0∞`, usada na instância `L^p`.

- [`Formalizacao.ModuloAbs`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 22.
- [`Formalizacao.ModuloAbs.realization`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 41.
- [`Formalizacao.ModuloAbs.stratum`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 46.
- [`Formalizacao.ModuloAbs.besov`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 50.
- [`Formalizacao.memℓp_of_succ_le`](../lean4/formalizacao/Formalizacao/Modulo.lean) — linha 102.

### F2 — arcabouço abstrato em $\mathbb R_{\ge0}^\infty$ e sua instância $L^p$

Texto: [conjecturas_lp.tex:722](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. A instância usa o subgrupo `MeasSub` das funções mensuráveis, com `nrm = eLpNorm · p vol01` e `ω = wtP p`. Os teoremas de conexão mostram que `realE`, `stratumE` e `besovE` coincidem com `realP`, `stratumP` e `besovP` para funções mensuráveis.

- [`Formalizacao.ModE.realE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 38.
- [`Formalizacao.ModE.stratumE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 42.
- [`Formalizacao.ModE.besovE`](../lean4/formalizacao/Formalizacao/ModuloENN.lean) — linha 47.
- [`FormalizacaoLp.MeasSub`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 22.
- [`FormalizacaoLp.realE_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 43.
- [`FormalizacaoLp.stratum_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 52.
- [`FormalizacaoLp.besov_conn`](../lean4/formalizacao/Formalizacao/ModuloConn.lean) — linha 69.

### F3 — Jackson racional com altura explícita sobre dados nodais (Parte IV, Lema IV.4.1)

Texto: [conjecturas_lp.tex:722](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. O núcleo `jackson_nodal` aceita dados nodais $y_j$ com erro nodal controlado. A forma para dados pontuais recupera a estimativa de Jackson da Parte IV.

- [`Pendencias.Jackson.jackson_nodal`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 447.
- [`Pendencias.Jackson.atom_height_nodal`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 334.
- [`Pendencias.Jackson.rational_jackson_height`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 512.
- [`Pendencias.Jackson.rational_jackson_uniform_explicit`](../lean4/formalizacao/Pendencias/Jackson.lean) — linha 599.

### F4 — Arcabouço abstrato instanciado em $L^\infty$ (Parte IV)

Texto: [conjecturas_lp.tex:722](../conjecturas_lp.tex); rótulo `lp:sec:lean`.

Estado: **Formalizado e compilado**. O segundo módulo e a norma uniforme da Parte IV satisfazem os três axiomas; a desigualdade inversa e a inclusão $\mathscr R\subset B$ em $L^\infty$ são reobtidas dos teoremas abstratos.

- [`FormalizacaoInf.modInf`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 45.
- [`FormalizacaoInf.realE_modInf`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 51.
- [`FormalizacaoInf.inverse_realG_of_abstract`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 58.
- [`FormalizacaoInf.besovE_top_iff`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 74.
- [`FormalizacaoInf.besovE_fin_iff`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 90.
- [`FormalizacaoInf.besovQ_of_RGQ_abstract`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 117.
- [`FormalizacaoInf.besovInf_of_RGInf_abstract`](../lean4/formalizacao/Formalizacao/ModuloInf.lean) — linha 131.

## Resumo

| Estado | Entradas |
|---|---|
| Formalizado e compilado | 21 |
| Formalizado (definição) | 5 |
| Formalizado e compilado, condicional a $J_p$ | 2 |
