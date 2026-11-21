# Pendências de revisão final — decorrentes da auditoria E1/E2

Este arquivo acompanha `RELATORIO_E1_E2_CONCLUSIVO_4_FONTES.md`, preservado sem alterações. Registra pontos do relatório que devem ser reformulados ou conferidos antes de qualquer redação definitiva (E5/E6). Nenhum manuscrito, PDF, bibliografia, Lean ou teste foi modificado.

Referência: branch `pesquisa-minimax-altura`, base `a8c52ef5b49b404aa43e150cfc223733934e5f4d`.

## 1. Cota de codificação `O(N log N)` e a perda de `log N`

**Ponto.** O relatório (seções 3, 9 e P5) afirma que a biblioteca de altura "perde um fator `log N`" em relação à ordem ótima de bits. Isso excede o que foi demonstrado.

**O que está demonstrado.** A Proposição `lp:prop:bits` dá uma cota superior de `4N(c_H+1)` bits para descrever os elementos de `Σ_{N,H}` com um código de comprimento fixo por campo. Com `H≍N^{a}`, isso é `O(N log N)`. A cota inferior de entropia dá `L ≥ c_5N−1`. A diferença entre as duas cotas é um fator `log N`.

**O que não está demonstrado.** Que *toda* codificação da biblioteca necessariamente custe `Ω(N log N)` bits. Uma cota superior de código não é uma cota inferior de custo. Não foi investigado se um código de comprimento variável (por exemplo, com endereços diferenciais, como o de Kerkyacharian–Picard) descreve `Σ_{N,H}` com `O(N)` bits, nem se `log_2|Σ_{N,H}|` é de fato da ordem de `N log N` (a contagem de cardinalidade da biblioteca não foi feita em sentido inferior).

**Reformulação a fazer.** Escrever que a codificação de comprimento fixo da Prop. `lp:prop:bits` fornece `O(N log N)` bits, enquanto a cota de entropia fornece `Ω(N)`; que a lacuna de `log N` entre as duas cotas é uma limitação dessa codificação, e que não se afirma que ela seja intrínseca à biblioteca.

## 2. Spline de DeVore–Popov e a biblioteca racional

**Ponto.** O relatório (seção 8, linha da tabela de DeVore–Popov, e a linha correspondente da matriz na seção 13) usa a notação `Σ_{n,∞} ⊃ T_k` e fala em "inclusão". Não afirmar inclusão exata.

**Razão.** `T_k(f)=Q_k(S_k(f))` (DeVore–Popov, Teor. 4.5) tem valores nodais reais. Os segmentos da biblioteca têm valor central e inclinação racionais, com altura `≤H`, inclinação não nula e endereço da folha terminal limitado. Um elemento de `T_k` não pertence a `Σ_{n,H}` em geral.

**Reformulação a fazer.** Dizer que o termo `N^{-s}` da cota superior segue do Teorema 4.5 *após racionalização* dos valores nodais e controle das alturas (valor central, inclinação e endereço), e que essa racionalização é o conteúdo dos lemas do manuscrito (`lp:lem:nodal-general`, `lp:lem:nodal-jump`, `lp:lem:nodal-variable-height`). A relação é de dedução com um passo adicional, não de inclusão de famílias.

## 3. Elbrächter et al.: mesmo calibre aritmético contra qualquer quantização

**Ponto.** Em vários trechos do relatório (resumo executivo, P1, seção 4 e a linha de Elbrächter na seção 8) a ausência de "restrição aritmética" ou de "parâmetro de altura" pode ser lida como ausência de qualquer quantização. Isso não é o caso.

**Distinção a manter.**
- Elbrächter et al. controlam quantização de pesos: pesos `(m,ε)`-quantizados, com precisão que cresce como uma potência de `log ε⁻¹`, e conectividade `M(Φ)`. A quantização existe e é central ao resultado.
- O manuscrito controla um calibre aritmético diferente: altura `max{|a|,b}` dos valores centrais e das inclinações racionais, mais o endereço diádico da folha, em funções contínuas com `≤N` folhas.
- Cohen et al. e Kerkyacharian–Picard também quantizam coeficientes (por planos de bits ou por limiar `λ`).

**Reformulação a fazer.** Substituir "sem restrição aritmética" por "sem o mesmo calibre aritmético" onde se refere a esses trabalhos, e especificar o recurso que cada um controla. Manter a conclusão de que não há redução demonstrada entre os modelos, sem sugerir que Elbrächter et al. ignorem a quantização.

## 4. Referências a conferir: Cohen et al. e Elbrächter et al.

Conferir contra as fontes (PDF ou página do periódico) antes de incluir em `conjecturas_lp_referencias.tex`:

| Fonte | Dados registrados no relatório | A conferir |
|---|---|---|
| Cohen, Dahmen, Daubechies, DeVore | *Appl. Comput. Harmon. Anal.* 11(2), 2001, p. 192–226, DOI 10.1006/acha.2001.0336. PDF examinado: cabeçalho `11, 192–226 (2001)` e `doi:10.1006/acha.2001.0336` conferidos. | Número do fascículo (2), mês, chave de citação `lp-cohen2001` (proposta) |
| Elbrächter, Perekrestenko, Grohs, Bölcskei | *IEEE Trans. Inf. Theory* 67(5), 2021, a partir da p. 2581; arXiv:1901.02220. | Página final, DOI, mês, chave de citação `lp-elbrachter2021` (proposta). O relatório deixa a página final em aberto. |

Chaves já presentes e que não exigem nova entrada: `artigo_2-devorepopov1988`, `lp-kerkyacharianpicard2003`, `lp-yang2024`, `lp-siegel2023`, `lp-oliveiravol`. Conferir também se Ou–Schenkel–Bölcskei (arXiv:2405.01952) será citado e, se for, criar a entrada.

Os quatro PDFs externos analisados (Yang, Cohen et al., DeVore–Popov, Kerkyacharian–Picard) **não foram adicionados ao repositório**. Suas referências estão na seção 2 e na seção 15 do relatório.

## 5. Lei conjunta `C²` e o Teorema 5.2

**Ponto.** O relatório (seção 11) observa que, em `s=2`, a fórmula `N^{-s}+H^{-s/a}` com `a=s` dá `N^{-2}+H^{-1}`. Essa observação é uma coincidência de forma, não uma identificação.

**Registro a manter.** A lei conjunta `E_{N,H}(F_{R,M}) ≍ N^{-2}+H^{-1}`, com `F_{R,M}={f∈C²[0,1]:‖f‖∞≤R,‖f''‖∞≤M}`, é consequência de resultados anteriores da Biblioteca Determinística (`artigo_2:thm:joint-budget`, parte dyadic) combinados com um piso quadrático elementar e o piso aritmético. A classe `C²` não é a classe `B^s_{p,q}` do Teorema 5.2, cuja hipótese é `0<s<2`.

**Reformulação a fazer.** Atribuir a lei `C²` à Parte II e a seus pisos elementares. Não descrevê-la como caso `s=2` do Teorema 5.2 e não usar a fórmula do Teorema 5.2 como enunciado do caso `C²`. Se o manuscrito mencionar a coincidência de forma, apresentá-la como observação, com a ressalva de que as classes são diferentes.

## Estado do repositório no momento deste registro

- Relatórios E3/E4 e mapas de formalização preservados, sem alterações: `RELATORIO_CORRECOES_E3_E4.md`, `RELATORIO_VALIDACAO_ETAPA_2.md`, `RELATORIO_VALIDACAO_INTEGRACAO.md`, `AUDITORIA_INTEGRACAO.md`, `mapas/MAPA_TEX_LEAN.md`, `mapas/AUDITORIA_FIDELIDADE.md`, `mapas/dados/mapa_lp.json`, `mapas/gerar_mapa.py`, `mapas/verificar_mapa.py`.
- Manuscritos LaTeX, PDFs, bibliografia, Lean e testes: não modificados.
