import Formalizacao

/-!
# Auditoria de axiomas

Cada `#print axioms` abaixo deve listar somente `propext`, `Classical.choice` e `Quot.sound`
e nunca `sorryAx`. Executar: `lake env lean Formalizacao/Auditoria.lean`.
-/

-- Arcabouço abstrato (valores reais)
#print axioms Formalizacao.inverse_le
#print axioms Formalizacao.realization_le_norm
#print axioms Formalizacao.stratum_subset_besov
-- Arcabouço abstrato (ENNReal)
#print axioms Formalizacao.ModE.inverse_E
#print axioms Formalizacao.ModE.stratum_subset_besovE
-- Módulo em L^p
#print axioms FormalizacaoLp.wtP_add_le
#print axioms FormalizacaoLp.wtP_le_four
#print axioms FormalizacaoLp.wtP_mono_t
#print axioms FormalizacaoLp.wtP_le_four_realP
#print axioms FormalizacaoLp.realE_conn
#print axioms FormalizacaoLp.stratum_conn
#print axioms FormalizacaoLp.besov_conn
#print axioms FormalizacaoLp.wtP_le_four_realP_of_abstract
#print axioms FormalizacaoLp.stratum_subset_besov_conn
#print axioms FormalizacaoLp.measurable_sigma
#print axioms FormalizacaoLp.classNH_subset_sigma
-- Reduções
#print axioms FormalizacaoRed.realP_le_norm
#print axioms FormalizacaoRed.realP_le_of_approx
#print axioms FormalizacaoRed.besov_subset_stratum
#print axioms FormalizacaoThm.conj1_endpoint_of_J
#print axioms FormalizacaoThm.conj1_subcritical_of_J
#print axioms FormalizacaoThm.conj1_critical_of_J
#print axioms FormalizacaoThm.conj1_tilde_of_J
#print axioms FormalizacaoStab.besov_subset_stratum_fam
#print axioms FormalizacaoStab.stability_iff_of_J
#print axioms FormalizacaoStab.conj2Stability_endpoint_of_J
#print axioms FormalizacaoStab.conj2Stability_subcritical_of_J
#print axioms FormalizacaoStab.conj2Stability_critical_of_J
#print axioms FormalizacaoStab.conj2Stability_tilde_of_J

-- M4: projeção afim local, Hölder, quase-interpolante e erro local
#print axioms FormalizacaoQuasi.abs_kL_le
#print axioms FormalizacaoQuasi.abs_kR_le
#print axioms FormalizacaoQuasi.integral_kL_mul_affine
#print axioms FormalizacaoQuasi.integral_kR_mul_affine
#print axioms FormalizacaoQuasi.abs_integral_kernel_le
#print axioms FormalizacaoGrid.lam_affine
#print axioms FormalizacaoGrid.Q_cell
#print axioms FormalizacaoGrid.Q_affine
#print axioms FormalizacaoGrid.abs_lam_le
#print axioms FormalizacaoGrid.local_error

-- M4(c), M5 (contingência), M6 (núcleo discreto)
#print axioms FormalizacaoQuasi.integral_abs_kL
#print axioms FormalizacaoQuasi.integral_abs_kR
#print axioms FormalizacaoQuasi.abs_integral_kL_mul_le
#print axioms FormalizacaoGrid.abs_lam_sup_le
#print axioms FormalizacaoCor.quasi_error
#print axioms FormalizacaoCor.local_error_inf
#print axioms FormalizacaoEmb.inverse_affine_sup
#print axioms FormalizacaoEmb.bernstein_affine

-- Lema 5.5 (M6)
#print axioms FormalizacaoL55c.ae_eq_Glim
#print axioms FormalizacaoL55c.Glim_continuousOn
#print axioms FormalizacaoL55c.Glim_bound
#print axioms FormalizacaoL55b.vk_sup_le
#print axioms FormalizacaoL55b.vk_slope_le
#print axioms FormalizacaoL55d.F_lip
#print axioms FormalizacaoL55e.modulus_lt1
#print axioms FormalizacaoL55e.modulus_eq1
#print axioms FormalizacaoL55e.modulus_gt1

-- Parte IV: refatoração de Jackson sobre dados nodais (M7)
#print axioms Pendencias.Jackson.jackson_nodal
#print axioms Pendencias.Jackson.atom_height_nodal
#print axioms Pendencias.Jackson.rational_jackson_height
#print axioms Pendencias.Jackson.rational_jackson_uniform_explicit

-- Lema 5.2(d) (M4)
#print axioms FormalizacaoL52d.lam_diff_le
#print axioms FormalizacaoL52d.omega1_ne_top

-- Lema 5.3 (Whitney em L^p, M5) e consequências incondicionais
#print axioms FormalizacaoW.whitney_lp
#print axioms FormalizacaoW.local_whitney
#print axioms FormalizacaoW.taylor_lp
#print axioms FormalizacaoW.fg_lp
#print axioms FormalizacaoW.double_sym
#print axioms FormalizacaoW.Wt_global
#print axioms FormalizacaoW.sum_lintegral_le
#print axioms FormalizacaoW.Ek_bound
#print axioms FormalizacaoW.quasi_error_unc
#print axioms FormalizacaoW.Glim_continuousOn_unc
#print axioms FormalizacaoW.ae_eq_Glim_unc
#print axioms FormalizacaoW.modulus_lt1_unc
#print axioms FormalizacaoW.modulus_eq1_unc
#print axioms FormalizacaoW.modulus_gt1_unc

-- M8: a hipótese J_p e as Conjecturas 1 e 2 como teoremas
#print axioms FormalizacaoJ.nodal_tree
#print axioms FormalizacaoJ.hypJp_of_lt
#print axioms FormalizacaoJ.hypJp_of_lt'
#print axioms FormalizacaoJ.conj1_endpoint
#print axioms FormalizacaoJ.conj1_subcritical
#print axioms FormalizacaoJ.conj1_critical
#print axioms FormalizacaoJ.conj1_tilde
#print axioms FormalizacaoJ.conj2_endpoint
#print axioms FormalizacaoJ.conj2_subcritical
#print axioms FormalizacaoJ.conj2_critical
#print axioms FormalizacaoJ.conj2_tilde
#print axioms FormalizacaoJ.Q_node
#print axioms FormalizacaoJ.lam_congr_ae
#print axioms FormalizacaoJ.nodal_G

-- L^∞ sobre o arcabouço abstrato (M1) e J_p com as constantes do artigo (M8)
#print axioms FormalizacaoInf.nInf_sub
#print axioms FormalizacaoInf.omega2_add_le
#print axioms FormalizacaoInf.realE_modInf
#print axioms FormalizacaoInf.inverse_realG_of_abstract
#print axioms FormalizacaoInf.besovE_top_iff
#print axioms FormalizacaoInf.besovE_fin_iff
#print axioms FormalizacaoInf.rG_eq
#print axioms FormalizacaoInf.besovQ_of_RGQ_abstract
#print axioms FormalizacaoInf.besovInf_of_RGInf_abstract
#print axioms FormalizacaoJ.lp_jackson_core
#print axioms FormalizacaoJ.hypJpStrong_of_lt
#print axioms FormalizacaoJ.besov_continuous_rep

-- Lema 5.1: núcleo = projeção em afins (fidelidade, correção 4)
#print axioms FormalizacaoKer.Kf_symm
#print axioms FormalizacaoKer.kL_eq_Kf
#print axioms FormalizacaoKer.kR_eq_Kf
#print axioms FormalizacaoKer.reproduce_affine
#print axioms FormalizacaoKer.range_affine
#print axioms FormalizacaoKer.kernel_is_affine_projection

-- Regimes s ≤ 1/p: Teoremas 3.1 (ii), (iii) e 3.2 nesses regimes
#print axioms FormalizacaoJ.nodal_tree_gen
#print axioms FormalizacaoJ.lp_jackson_low_core
#print axioms FormalizacaoLow.sum_le_lq
#print axioms FormalizacaoLow.step_le
#print axioms FormalizacaoLow.Q_sup_le
#print axioms FormalizacaoLow.lam_bound
#print axioms FormalizacaoLow.classNH_le_sigma
#print axioms FormalizacaoLow.jackson_low
#print axioms FormalizacaoLow.besov_subset_stratum_low
#print axioms FormalizacaoLow.lq_geom_all
#print axioms FormalizacaoLow.lq_poly_all
#print axioms FormalizacaoLow.wreal_geom
#print axioms FormalizacaoLow.wreal_poly
#print axioms FormalizacaoLow.mDiag_ge
#print axioms FormalizacaoLow.mDiag_le
#print axioms FormalizacaoLow.hshift_low
#print axioms FormalizacaoLow.hshift_diag
#print axioms FormalizacaoLow.hW_geom
#print axioms FormalizacaoLow.hW_poly
#print axioms FormalizacaoLow.sigma_family
#print axioms FormalizacaoLow.conj2_low
#print axioms FormalizacaoLow.conj2_diag
#print axioms FormalizacaoLow.conj1_low
#print axioms FormalizacaoLow.conj1_diag

-- Estabilidade aproximada (ramo Estabilidade)
#print axioms FormalizacaoStab.besov_subset_stratum_fam_approx
#print axioms FormalizacaoStab.stability_approx_iff_of_J
#print axioms FormalizacaoJ.conj2_approx_endpoint
#print axioms FormalizacaoJ.conj2_approx_subcritical
#print axioms FormalizacaoJ.conj2_approx_critical
#print axioms FormalizacaoJ.conj2_approx_tilde
#print axioms FormalizacaoLow.hW_diag
#print axioms FormalizacaoLow.besov_subset_stratum_low_core
#print axioms FormalizacaoLow.besov_subset_stratum_low_approx
#print axioms FormalizacaoLow.conj2_approx_low
#print axioms FormalizacaoLow.conj2_approx_diag

-- Seção 6: cotas uniformes
#print axioms FormalizacaoLow.lam_bound_unif
#print axioms FormalizacaoLow.qexp_le_of_target_le
#print axioms FormalizacaoLow.uniform_height_quantization
#print axioms FormalizacaoLow.uniform_quantWeight_lt_top
#print axioms FormalizacaoLow.uniform_besov_ball
#print axioms FormalizacaoRegular.uniform_quantWeight_zero_not_lt_top

-- Seção 6: piso aritmético e comprimento binário
#print axioms FormalizacaoFloor.rational_arithmetic_floor
#print axioms FormalizacaoFloor.arithmetic_floor_lp
#print axioms FormalizacaoFloor.arithmetic_floor_bestError
#print axioms FormalizacaoFloor.arithmetic_height_necessary
#print axioms FormalizacaoBits.coordinateWidth_eq
#print axioms FormalizacaoBits.treeWord_prefix
#print axioms FormalizacaoBits.boundedLibrary_code
#print axioms FormalizacaoBits.boundedLibrary_card
#print axioms FormalizacaoBits.boundedLibrary_log_card
#print axioms FormalizacaoBits.uniform_rate_bits

-- Seção 6: agendas regulares, log-log e séries de Bertrand
#print axioms FormalizacaoRegular.regular_schedule_criterion
#print axioms FormalizacaoLogLog.logLog_schedule_iff
#print axioms FormalizacaoLogLog.conj1_loglog
#print axioms FormalizacaoLogLog.conj2_loglog
#print axioms FormalizacaoLogLog.conj2_approx_loglog
#print axioms FormalizacaoLogLog.uniform_loglog_ball
#print axioms FormalizacaoLogLog.HlogLogDiag_eq
#print axioms FormalizacaoLogLog.conj1_loglog_diagonal
#print axioms FormalizacaoLogLog.logLog_schedule_ratio_tendsto_zero
#print axioms FormalizacaoIterated.bertrand_summable_iff
#print axioms FormalizacaoIterated.iterated_schedule_iff

/-! ## Auditoria de 20/11/2026: altura aritmética em Besov (`AlturaXxx.lean`) -/
-- Biblioteca e última folha
#print axioms FormalizacaoAltura.terminal_affine
#print axioms FormalizacaoAltura.classNH_lipschitz
-- Funções-teste e cotas de Besov
#print axioms FormalizacaoAltura.wtP_bumpS_le
#print axioms FormalizacaoAltura.eLpNorm_bumpS_le
#print axioms FormalizacaoAltura.besovNorm_bumpS_le
-- Pisos geométrico e de inclinação
#print axioms FormalizacaoAltura.L1_affine_lower
#print axioms FormalizacaoAltura.kappaB_pos
#print axioms FormalizacaoAltura.geometric_floor
#print axioms FormalizacaoAltura.two_interval_pointwise
#print axioms FormalizacaoAltura.slope_floor
-- Necessidade (erro e realização) e transferência
#print axioms FormalizacaoAltura.geometric_necessity
#print axioms FormalizacaoAltura.slope_necessity
#print axioms FormalizacaoAltura.arithmetic_necessity
#print axioms FormalizacaoAltura.bestError_le_realP
#print axioms FormalizacaoAltura.realP_le_bestError_add
#print axioms FormalizacaoAltura.geometric_necessity_realP
#print axioms FormalizacaoAltura.slope_necessity_realP
-- Quantização com salto J
#print axioms FormalizacaoAltura.quantization_jump
-- Altura linear crítica
#print axioms FormalizacaoCrit.nodal_jump
#print axioms FormalizacaoCrit.critical_approx
#print axioms FormalizacaoCrit2.critical_level
#print axioms FormalizacaoCrit3.critical_lq
#print axioms FormalizacaoCrit3.critical_rate
#print axioms FormalizacaoCrit3.critical_char_radius
#print axioms FormalizacaoAltura.quantization_jump
#print axioms FormalizacaoJ.nodal_tree_coarse
#print axioms FormalizacaoAltura.geometric_floor
#print axioms FormalizacaoAltura.geometric_necessity
#print axioms FormalizacaoAltura.slope_necessity
#print axioms FormalizacaoAltura.arithmetic_necessity
#print axioms FormalizacaoCrit4.critical_radius_ball_and_inclusion

-- F2: definições minimax, empacotamento de bumps e piso pelo número de folhas
#print axioms FormalizacaoMinimax.aPS_of_lt
#print axioms FormalizacaoMinimax.aPS_of_mid
#print axioms FormalizacaoMinimax.aPS_of_gt
#print axioms FormalizacaoMinimax.aPS_pos
#print axioms FormalizacaoMinimax.aPS_eq_nuHat
#print axioms FormalizacaoMinimax.le_Dfun
#print axioms FormalizacaoMinimax.le_bestError_of_forall
#print axioms FormalizacaoPacking.overlap_le_three
#print axioms FormalizacaoPacking.diff2_scaled
#print axioms FormalizacaoPacking.diff2_Fm_pow_le
#print axioms FormalizacaoPacking.lint_diff_le
#print axioms FormalizacaoPacking.Ipow_small_le
#print axioms FormalizacaoPacking.exists_K0
#print axioms FormalizacaoPacking.aTerm_le_low
#print axioms FormalizacaoPacking.aTerm_le_high
#print axioms FormalizacaoPacking.exists_Lq
#print axioms FormalizacaoPacking.packing_norm_le
#print axioms FormalizacaoLeaf.card_splits_le
#print axioms FormalizacaoLeaf.affine_on_open
#print axioms FormalizacaoLeaf.exists_good_cells
#print axioms FormalizacaoLeaf.cell_lower
#print axioms FormalizacaoLeaf.agg_lower
#print axioms FormalizacaoLeaf.leaf_dist_lower
#print axioms FormalizacaoLeaf.leaf_floor_const
#print axioms FormalizacaoLeaf.dfun_geometric_floor
#print axioms FormalizacaoLeaf.dfun_slope_floor
#print axioms FormalizacaoLeaf.dfun_arithmetic_floor
