# ARTIGO-BESOV

[![Artigo em PDF][selo-pdf]](conjecturas_lp.pdf)
[![Lean 4.28.0][selo-lean]](lean4/formalizacao/lean-toolchain)
[![Código sob Apache 2.0][selo-apache]](LICENSE)
[![Artigo sob CC BY 4.0][selo-cc]](LICENSES/CC-BY-4.0.txt)
[![Política de segurança][selo-security]](SECURITY.md)

**Caracterização dos espaços de Besov em $L^p$ por realização com altura aritmética controlada**

Victor Gabriel de Oliveira · 19 de novembro de 2026

[Original revisado](conjecturas_lp.pdf) · [Edição ABNT](conjecturas_lp_abnt.pdf) · [English edition](conjecturas_lp_en.pdf) · [Explorar o mapa TeX–Lean](mapas/MAPA_TEX_LEAN.md) · [Compilar e verificar](#como-verificar-de-forma-independente)

## Resultados do artigo

O artigo caracteriza os espaços de Besov $B^s_{p,q}([0,1])$, com $1\le p<\infty$, $0<s<2$ e $0<q\le\infty$, pela somabilidade diádica de um **funcional de realização**. O funcional combina o erro em $L^p$ com o módulo de suavidade de segunda ordem do aproximante. Os aproximantes são funções contínuas e afins por partes, com coeficientes racionais e partições diádicas. A construção limita o número de folhas e a altura aritmética.

- **Jackson racional em $L^p$.** Para $s>1/p$ e $f\in B^s_{p,\infty}$, a construção usa até $n$ folhas e altura no máximo $H$. Quando esses orçamentos são suficientemente grandes, o erro é limitado por $9C_W(p)\,\omega_2(f,n^{-1})_p + 16(\|f\|_\infty+1)/H$. A prova combina projeções afins locais, uma desigualdade de Whitney em partições e quantização nodal em grades alternadas.
- **Caracterização de Besov.** Para $s>1/p$, a agenda de altura parte de $N^{\max\{1,s\}}$, com correção logarítmica de expoente $\kappa>1/q$ quando $q<\infty$ e $s\ge1$. O controle dos quase-interpolantes permite tratar funções ilimitadas nos demais regimes, com agendas da ordem de $N^{1+1/p-s}$ para $s<1/p$ e de $N$ vezes uma potência de $\log N$ na diagonal $s=1/p$.
- **Estabilidade para redes ReLU.** A caracterização se transfere a famílias aninhadas que contêm a biblioteca racional após reescalonar linearmente o orçamento. O Teorema 3.3 admite inclusão aproximada em $L^p$ com tolerâncias tais que $(2^{rs}\varepsilon_{2^r})\in\ell^q$.
- **Cotas uniformes e complexidade em bits.** A seção 6 demonstra cotas uniformes em bolas de Besov, um piso aritmético em $L^p$, um código de árvores livre de prefixo e um critério para agendas de log iterado. Na série de Bertrand, o limiar de convergência é $\gamma q>1$.

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

A saída esperada é vazia.

### 4. Auditar os axiomas

Ainda em `lean4/formalizacao/`, execute:

```bash
lake env lean Formalizacao/Auditoria.lean
```

A saída esperada tem 170 linhas, todas com `[propext, Classical.choice, Quot.sound]`. Para comparar com o arquivo versionado na mesma execução, use a forma abaixo. A comparação também detecta declarações ausentes e ocorrências de `sorryAx`.

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

## Escopo da formalização

- Os Teoremas 3.1 e 3.2 estão formalizados nos três regimes, e o Teorema 3.3 cobre a inclusão aproximada. Os módulos `Formalizacao/Low*.lean` tratam $s\le1/p$ com constantes de Jackson que podem depender de $f$.
- O Lean usa representantes mensuráveis $\mathbb R\to\mathbb R$ e a medida de Lebesgue restrita a $[0,1]$. Os casos com agenda $\widetilde H_{s,\eta}$ assumem $1/p<s<2$.
- As reduções usam a estimativa de Jackson com constantes que podem depender de $f$. A forma com constantes explícitas $C_0=9C_W(p)$ e $C_1=16$ está em [`hypJpStrong_of_lt`](lean4/formalizacao/Formalizacao/LpJackson4.lean).
- A auditoria de fidelidade compara os enunciados e registra as escolhas de formalização, incluindo a referência externa usada no resultado de entropia métrica da seção 6. [Consultar a auditoria de fidelidade](mapas/AUDITORIA_FIDELIDADE.md)

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
