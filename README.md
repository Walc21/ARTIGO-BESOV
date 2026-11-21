# ARTIGO-BESOV

[![Artigo em PDF][selo-pdf]](conjecturas_lp.pdf)
[![Lean 4.28.0][selo-lean]](lean4/formalizacao/lean-toolchain)
[![Código sob Apache 2.0][selo-apache]](LICENSE)
[![Artigo sob CC BY 4.0][selo-cc]](LICENSES/CC-BY-4.0.txt)
[![Política de segurança][selo-security]](SECURITY.md)

**Lei minimax para aproximação de Besov com folhas diádicas e altura aritmética**

Victor Gabriel de Oliveira · 21 de novembro de 2026

[Original revisado](conjecturas_lp.pdf) · [Edição ABNT](conjecturas_lp_abnt.pdf) · [English edition](conjecturas_lp_en.pdf) · [Explorar o mapa TeX–Lean](mapas/MAPA_TEX_LEAN.md) · [Compilar e verificar](#como-verificar-de-forma-independente)

## Resultados do artigo

O artigo determina o pior erro de aproximação na bola unitária de $B^s_{p,q}([0,1])$ para dois orçamentos independentes. O número $N$ limita as folhas de uma árvore diádica e $H$ limita a altura aritmética de cada folha. Os aproximantes são montagens contínuas de segmentos afins racionais.

- **Lei minimax.** Para $1\le p<\infty$, $0<s<2$ e $0<q\le\infty$, o erro tem ordem $N^{-s}+H^{-s/a(p,s)}$. A potência $a(p,s)$ é $1+1/p-s$ para $s<1/p$, $1$ para $1/p\le s\le1$ e $s$ para $s>1$. Os pisos valem para árvores adaptativas. As construções usam malhas uniformes. A mesma lei vale para o funcional de realização.
- **Jackson e quantização.** As projeções afins locais e a desigualdade de Whitney controlam os erros de quase-interpolação. Em $p=s=1$, denominadores diádicos por nó eliminam o fator logarítmico da taxa por escala.
- **Caracterização por realização.** Na diagonal $s=1/p$ com $p>1$, qualquer agenda $\max\{2,\lceil A_*N\rceil\}$ com $A_*>0$ dá a igualdade de conjuntos para todo $q$, inclusive $q=\infty$. A norma da sequência cresce, no pior caso na bola, como $B^{1+1/p}$ para raios grandes. Para $p=s=1$ com $q<\infty$, continua em aberto a caracterização com agenda linear.
- **Estabilidade e codificação.** A caracterização se transfere a famílias aninhadas de redes ReLU por inclusão exata ou aproximação com tolerância somável. O texto dá um código livre de prefixo, cotas inferiores de entropia e agendas de log iterado.

O apêndice do artigo descreve a formalização em Lean 4 e a correspondência entre as demonstrações e as declarações verificadas.

## Onde encontrar cada parte

| Caminho | Descrição |
|---|---|
| [PDF](conjecturas_lp.pdf) · [Fonte LaTeX](conjecturas_lp.tex) | Edição original revisada, com apêndice sobre a formalização. |
| [PDF ABNT](conjecturas_lp_abnt.pdf) · [Fonte LaTeX](conjecturas_lp_abnt.tex) | Edição em português no formato ABNT para artigo científico. |
| [PDF em inglês](conjecturas_lp_en.pdf) · [Fonte LaTeX](conjecturas_lp_en.tex) | Tradução integral da edição original para o inglês. |
| [`lean4/formalizacao/`](lean4/formalizacao/) | Projeto Lake com Lean 4.28.0 e Mathlib v4.28.0. |
| [`Formalizacao.lean`](lean4/formalizacao/Formalizacao.lean) · [`Formalizacao/`](lean4/formalizacao/Formalizacao/) | Ponto de entrada e módulos com as demonstrações principais. |
| [`Pendencias/`](lean4/formalizacao/Pendencias/) · [`RequestProject/`](lean4/formalizacao/RequestProject/) | Módulos auxiliares dos quais `Formalizacao` depende. |
| [`Auditoria.lean`](lean4/formalizacao/Formalizacao/Auditoria.lean) · [saída da auditoria](lean4/formalizacao/auditoria_axiomas.txt) | Comandos de inspeção e axiomas de cada declaração auditada. |
| [`mapas/`](mapas/) | Dados e scripts do mapa, [correspondência TeX–Lean](mapas/MAPA_TEX_LEAN.md) e [auditoria de fidelidade](mapas/AUDITORIA_FIDELIDADE.md). |
| [`auditorias/`](auditorias/) | Relatórios das auditorias de originalidade (E1/E2), da integração bibliográfica e da consolidação editorial (E5/E6), com as pendências registradas. |

## Como verificar de forma independente

Comece na raiz do repositório. Para obter uma cópia local, use:

```bash
git clone https://github.com/Walc21/ARTIGO-BESOV.git
cd ARTIGO-BESOV
```

### 1. Compilar os PDFs

Use uma versão recente do TeX Live com `latexmk`, `pdflatex`, `babel` com suporte a português e inglês, as fontes Latin Modern e TeX Gyre e os pacotes indicados em [conjecturas_lp_estilo.sty](conjecturas_lp_estilo.sty). Em Debian e Ubuntu, a lista de pacotes inclui `latexmk`, `texlive-latex-base`, `texlive-latex-extra`, `texlive-fonts-recommended`, `texlive-lang-portuguese`, `tex-gyre` e `lmodern`.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  conjecturas_lp.tex conjecturas_lp_abnt.tex conjecturas_lp_en.tex
```

Os PDFs são gerados na raiz. O `latexmk` repete a compilação até resolver as referências cruzadas. A edição ABNT carrega a fonte em português, e as três versões compartilham o estilo, os dados de citação e a bibliografia.

A edição ABNT segue a NBR 6022:2018 para a estrutura do artigo, a NBR 6024:2012 para as seções, a NBR 6028:2021 para os resumos, a NBR 10520:2023 para as citações e a NBR 6023:2025 para as referências. Os campos de contato e das datas oficiais de submissão e aprovação estão em [conjecturas_lp_abnt.tex](conjecturas_lp_abnt.tex) e aguardam esses dados.

### 2. Instalar o Lean

Instale o `elan` caso ainda precise de um gerenciador de versões do Lean. Ele lê [`lean-toolchain`](lean4/formalizacao/lean-toolchain) para selecionar `leanprover/lean4:v4.28.0`.

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Abra um novo terminal se precisar carregar o `PATH` atualizado e volte à raiz do repositório.

### 3. Compilar a formalização

O [`lake-manifest.json`](lean4/formalizacao/lake-manifest.json) fixa as revisões das dependências. O primeiro comando do Lake obtém o cache pré-compilado da Mathlib v4.28.0.

```bash
cd lean4/formalizacao
lake exe cache get
lake build Formalizacao
```

A compilação deve terminar com `Build completed successfully`. Para conferir ocorrências da palavra `sorry` nos módulos de `Formalizacao`, use:

```bash
grep -rnw 'sorry' Formalizacao/ Formalizacao.lean
```

A única ocorrência esperada é o comentário ``nenhum resultado depende de `sorry` `` em `Formalizacao/AlturaBump.lean`, linha 13. Não há `sorry` em demonstrações.

### 4. Auditar os axiomas

Ainda em `lean4/formalizacao/`, execute:

```bash
lake env lean Formalizacao/Auditoria.lean
```

A saída esperada tem 201 linhas para 196 declarações distintas e registra somente os axiomas `propext`, `Classical.choice` e `Quot.sound`. Para comparar com o arquivo versionado na mesma execução, use a forma abaixo. A comparação também detecta declarações ausentes e ocorrências de `sorryAx`.

```bash
set -o pipefail
lake env lean Formalizacao/Auditoria.lean | diff -u auditoria_axiomas.txt -
```

O `diff` deve terminar com código zero e sem saída.

### 5. Conferir a correspondência TeX–Lean

Volte à raiz do repositório. Com Python 3 e o projeto Lean já compilado, execute:

```bash
python3 mapas/verificar_mapa.py
```

O script verifica os rótulos do TeX, confirma os nomes das declarações com `#check` no Lean e compara o mapa versionado com a versão gerada.

### 6. Executar os testes da Etapa 2

Na raiz, execute:

```bash
python3 -B -m unittest discover -s testes -v
```

A suíte usa frações exatas para testar a construção nodal e confere a correspondência editorial entre português, inglês e ABNT. Os comandos e resultados da integração estão no [relatório de validação da Etapa 2](RELATORIO_VALIDACAO_ETAPA_2.md).

## Escopo da formalização

- Os Teoremas 6.1 e 6.2 estão formalizados nos três regimes, e o Teorema 6.3 cobre a inclusão aproximada. Os módulos `Formalizacao/Low*.lean` tratam $s\le1/p$ com constantes de Jackson que podem depender de $f$.
- O Lean usa representantes mensuráveis $\mathbb R\to\mathbb R$ e a medida de Lebesgue restrita a $[0,1]$. Os casos com agenda $\widetilde H_{s,\eta}$ assumem $1/p<s<2$.
- As reduções usam a estimativa de Jackson com constantes que podem depender de $f$. A forma com constantes explícitas $C_0=9C_W(p)$ e $C_1=16$ está em [`hypJpStrong_of_lt`](lean4/formalizacao/Formalizacao/LpJackson4.lean).
- O minimax em dois orçamentos, o quantizador por nó, a extensão sequencial crítica a $q=\infty$, a agenda linear fixa e o crescimento ótimo no raio têm provas analíticas no artigo. A formalização existente cobre lemas de apoio e o teorema crítico por bola para $q$ finito.
- A auditoria de fidelidade compara os enunciados e registra as escolhas de formalização, incluindo, para o estado anterior ao commit `9951091`, a referência externa usada na entropia métrica da seção 6. A cota inferior de entropia agora tem demonstração própria no artigo (ver a seção de atualização da auditoria). [Consultar a auditoria de fidelidade](mapas/AUDITORIA_FIDELIDADE.md)

## Licenças e segurança

- **Código Lean e scripts Python** sob Apache License 2.0. [Texto da licença](LICENSE)
- **Artigo em LaTeX e PDF, documentação e mapas** sob Creative Commons Atribuição 4.0 Internacional. [Texto da licença](LICENSES/CC-BY-4.0.txt)
- **Atribuição e escopo das licenças.** [Avisos de direitos autorais](NOTICE)
- **Relato de vulnerabilidades.** [Política de segurança](SECURITY.md)

[selo-pdf]: https://img.shields.io/badge/Artigo-PDF-1d4ed8?style=for-the-badge
[selo-lean]: https://img.shields.io/badge/Lean-4.28.0-6d28d9?style=for-the-badge
[selo-apache]: https://img.shields.io/badge/C%C3%B3digo-Apache_2.0-0e7490?style=for-the-badge
[selo-cc]: https://img.shields.io/badge/Artigo-CC_BY_4.0-0f766e?style=for-the-badge
[selo-security]: https://img.shields.io/badge/Seguran%C3%A7a-Pol%C3%ADtica-475569?style=for-the-badge
