# Relatório de integração E1/E2 (Etapa 4B.4)

Integração, nas três edições e na bibliografia, das conclusões verificadas da auditoria E1/E2. Esta etapa é independente de E5/E6, que **não foram iniciados**.

- Branch: `pesquisa-minimax-altura`. Commit de partida: `bf530161744467b9ae70b1ea5220e7c268f70424`. Árvore limpa no início.
- Fontes lidas antes de editar: `auditorias/PENDENCIAS_REVISAO_FINAL.md` (integral), `auditorias/RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md` (seções 3, 5–7, 9–11, 14, 15, 17), as três edições, `conjecturas_lp_referencias.tex` e `conjecturas_lp_citacoes.tex`.

## 1. Arquivos modificados

| Arquivo | Alteração |
|---|---|
| `conjecturas_lp.tex` | 3 linhas substituídas no lugar: parágrafo de contexto da introdução (linha 55), observação `lp:obs:entropy` (1384) e última frase das Considerações finais (1392). |
| `conjecturas_lp_en.tex` | As 3 passagens equivalentes (linhas 26, 1354 e 1362). |
| `conjecturas_lp_referencias.tex` | 3 entradas novas; entrada `lp-oliveiravol` passa a indicar "Partes II e IV". |
| `conjecturas_lp_citacoes.tex` | 3 entradas novas. |
| `auditorias/PENDENCIAS_REVISAO_FINAL.md` | Seção de status acrescentada ao final; histórico preservado. |
| `auditorias/RELATORIO_INTEGRACAO_E1_E2.md` | Este relatório. |

`conjecturas_lp_abnt.tex` não foi alterado: a edição ABNT continua carregando `conjecturas_lp.tex` por `\input`. `README.md` não precisou de alteração: nenhuma afirmação científica ou referência dele ficou inconsistente com o texto revisado. As edições foram feitas **sem mudar o número de linhas** de `conjecturas_lp.tex`, de modo que as linhas de rótulos usadas pelo mapa TeX–Lean permanecem válidas (os parágrafos novos usam `\par` dentro da mesma linha de código-fonte).

## 2. Citações adicionadas

| Chave | Fonte | Dados | Estado da verificação |
|---|---|---|---|
| `lp-cohen2001` | Cohen, Dahmen, Daubechies, DeVore. *Tree approximation and optimal encoding*. ACHA | v. 11, n. 2, p. 192–226, 2001, DOI 10.1006/acha.2001.0336 | Volume, páginas e DOI conferidos no cabeçalho do PDF examinado; número do fascículo conferido em registro do periódico (busca). |
| `lp-elbrachter2021` | Elbrächter, Perekrestenko, Grohs, Bölcskei. *Deep neural network approximation theory*. IEEE TIT | v. 67, n. 5, p. 2581–2623, 2021; arXiv:1901.02220 | Volume, número e páginas conferidos em registro do periódico (busca). **DOI não foi verificado e não foi incluído.** O PDF do arXiv não traz a referência do periódico. |
| `lp-birmansolomyak1967` | Birman, Solomyak. *Piecewise polynomial approximation of functions of the classes `W_p`*. Mat. Sb. | v. 73, p. 295–317, 1967 | Dados conforme as listas de referências de Cohen et al. (ref. 3) e de Kerkyacharian–Picard (ref. 4), que concordam. **Original não consultado.** |

Chaves já existentes e agora também usadas no novo texto: `artigo_2-devorepopov1988`, `lp-kerkyacharianpicard2003`, `lp-siegel2023`, `lp-yang2024`, `lp-oliveiravol`, `lp-ali2020`, `artigo_1-devore2021`. Siegel e Yang saíram do último grupo de citação do parágrafo de redes e passaram a ser citados nominalmente.

Nos três casos novos, a lista de autores segue o padrão do estilo (`\abntentry`); para Cohen et al. e Elbrächter et al. (quatro autores) usou-se "et al.".

## 3. Correção das cinco pendências

1. **`O(N log N)` contra `Ω(N)` de bits.** Última frase das Considerações finais (PT 1392, EN 1362): a diferença é a lacuna entre a cota superior do código de comprimento fixo da `lp:prop:bits` e a cota inferior de entropia; o texto declara que não afirma `Ω(N log N)` em toda codificação. A frase anterior do manuscrito já distinguia as duas ordens. Resolvida.
2. **Spline de DeVore–Popov.** Introdução: a estimativa direta é "o ponto de partida do termo `N^{-s}`", e a passagem às montagens racionais "exige racionalizar os valores nodais e controlar as alturas". Não se afirma inclusão. Resolvida.
3. **Quantização contra calibre aritmético.** Introdução: Cohen et al., Birman–Solomyak e Kerkyacharian–Picard "quantizam coeficientes e medem o custo em bits, mas não impõem altura limitada" ao valor central e à inclinação; Siegel e Yang usam parâmetros reais; Elbrächter et al. usam pesos quantizados em precisão da ordem de uma potência de `log ε⁻¹`, com erro em `L²`. O texto conclui que os modelos diferem e que o artigo não estabelece redução. Resolvida.
4. **Referências.** Ver seção 2. Resolvida, com duas conferências abertas (DOI de Elbrächter et al.; páginas de Birman–Solomyak no original).
5. **Lei `C²`.** Introdução: a Parte II constrói montagens com `n` folhas e altura de ordem `n²` em grades racionais alternadas; a lei conjunta `N^{-2}+H^{-1}` nessa classe "decorre" dessa construção combinada com os pisos aritmético e quadrático, é consequência de resultados anteriores e não se confunde com o caso `s=2` do Teorema 5.2, cuja hipótese é `0<s<2`. Resolvida.

## 4. Trechos científicos alterados

**Introdução (PT 55 / EN 26).** O parágrafo único de contexto foi reescrito em quatro blocos: (a) antecedentes de DeVore–Popov e racionalização; (b) árvores e codificação (Cohen et al.), entropia (Birman–Solomyak, Kerkyacharian–Picard) e a razão pela qual não fornecem a lei em `(N,H)`; (c) a Biblioteca Determinística (Partes II e IV), a lei `C²` e a contribuição do Teorema 5.2; (d) redes ReLU (Ali–Nouy, DeVore–Hanin–Petrova, Siegel, Yang, Elbrächter et al.) e a ausência de redução entre modelos. Frases preexistentes sobre funcionais de realização, Parte IV e o papel da norma `L^p` foram mantidas.

**Observação `lp:obs:entropy` (PT 1384 / EN 1354).** Acrescentada a atribuição da ordem `ε^{-1/s}` a Birman–Solomyak, Kerkyacharian–Picard e Cohen et al. (Teorema 1.1), a relação `H_ε ≤ R`, a declaração de que a `lp:prop:entropy-lower` e o `lp:cor:bits-lower` não reivindicam novidade nessa ordem (e sim constantes explícitas para a definição por módulos de suavidade), e a origem do empacotamento (hipercubo de bumps e cota de Varshamov–Gilbert).

**Considerações finais (PT 1392 / EN 1362).** Frase sobre a lacuna `N log N` contra `N`.

## 5. Resultados dos testes e verificações

| Verificação | Resultado |
|---|---|
| `python3 -m unittest discover -s testes -v` | 9 testes, todos OK (inclui `test_referencias_e_citacoes_resolvidas`, `test_rotulos_unicos_e_na_mesma_ordem`, `test_abnt_compartilha_a_fonte_portuguesa`). `pytest` não está instalado; usou-se `unittest`. |
| `python3 mapas/verificar_mapa.py` | 64 entradas e 263 nomes Lean localizados; o Lean aceitou todos os nomes (`#check`); `MAPA_TEX_LEAN.md` está atualizado. Código Lean não foi alterado nem reconstruído (nenhum módulo Lean foi tocado). |
| Compilação `conjecturas_lp.tex`, `conjecturas_lp_en.tex`, `conjecturas_lp_abnt.tex` com `latexmk -pdf -halt-on-error` | As três terminaram com código 0 (30, 31 e 33 páginas). Compilação feita em diretório separado (`-outdir`), sem tocar nos PDFs rastreados. |
| Referências ou citações indefinidas, erros LaTeX | Nenhum erro; nenhuma citação ou referência indefinida nos três logs; nenhum `??` no texto extraído dos três PDFs; nenhum aviso de pacote nem `Overfull` nos logs. |
| Enunciados, hipóteses, constantes, fórmulas e demonstrações | Comparação contra `bf53016`: nas duas edições, os 109 blocos matemáticos (teorema, lema, proposição, corolário, definição, demonstração, equações e enumerações) e as 81 fórmulas em display são idênticos, excluindo apenas o texto das observações; os rótulos coincidem; o número de linhas é o mesmo (1472 em PT, 1438 em EN). Somente as 3 linhas citadas mudaram em cada arquivo. |
| Equivalência PT/EN | Nas três passagens editadas, as chaves de citação, as referências cruzadas, o número de `\par` e o conjunto de fórmulas em linha coincidem entre PT e EN. A equivalência de significado foi conferida por leitura. |

## 6. Limitações remanescentes

1. **DOI de Elbrächter et al.** não verificado; omitido da entrada.
2. **Birman–Solomyak:** dados copiados das listas de referências de Cohen et al. e Kerkyacharian–Picard; páginas e periódico não conferidos no original (as páginas 295–317 podem corresponder à tradução inglesa).
3. **Lei `C²`.** O manuscrito a afirma como consequência da Parte II com pisos aritmético e quadrático, mas a dedução está só no relatório de auditoria (seção 11 de `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md`). Para E5/E6, avaliar se convém incluir a dedução curta como observação ou suavizar o verbo "decorre".
4. **Relatório preservado.** `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md` mantém as formulações originais (perda de `log N`, `Σ_{n,∞} ⊃ T_k`, "sem restrição aritmética", coincidência de forma com `s=2`), conforme a instrução de preservação integral.
5. **PDFs rastreados** (`conjecturas_lp.pdf`, `conjecturas_lp_en.pdf`, `conjecturas_lp_abnt.pdf`) **não foram regenerados** e anteciparam este texto; os PDFs compilados nesta etapa estão fora do repositório. Regenerar os PDFs rastreados é decisão de uma etapa posterior.
6. A integração reflete a auditoria como ela está. As lacunas da auditoria (DeVore–Howard–Micchelli, demonstrações completas de Kerkyacharian–Picard e Cohen et al., releitura de Siegel, Elbrächter e Ou et al.) continuam registradas em `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md`, seção 16, e não foram transformadas em afirmações do manuscrito.

## 7. Diff resumido

```
 auditorias/PENDENCIAS_REVISAO_FINAL.md |  16 ++++++++++++++++
 conjecturas_lp.tex                     |   6 +++---
 conjecturas_lp_citacoes.tex            |   3 +++
 conjecturas_lp_en.tex                  |   6 +++---
 conjecturas_lp_referencias.tex         |   5 ++++-
 (+ auditorias/RELATORIO_INTEGRACAO_E1_E2.md, novo)
```

Linhas alteradas: PT 55, 1384, 1392; EN 26, 1354, 1362. Referências: 3 entradas novas e uma alteração de texto em `lp-oliveiravol` ("Parte IV" para "Partes II e IV", nas duas línguas).

## 8. Estado de E5/E6

E5/E6 (revisão editorial geral) não foram iniciados. Nenhuma refatoração, reformatação ou revisão de estilo fora das passagens acima foi feita.
