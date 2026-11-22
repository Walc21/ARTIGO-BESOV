#!/usr/bin/env bash
set -eu
evidence_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
checkout_dir="${1:?Informe o caminho da cópia isolada no SHA auditado}"
cd "$checkout_dir"
test "$(git rev-parse HEAD)" = 19c85be8bd08098b4a8c6d0452e755b5e3683be7
test -z "$(git status --porcelain)"
cd lean4/formalizacao
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
printf '%s\n' 'lake build Formalizacao'
lake build Formalizacao > "$evidence_dir/build.log" 2>&1
printf '%s\n' 'lake build RequestProject Pendencias'
lake build RequestProject Pendencias > "$evidence_dir/build-completo.log" 2>&1
printf '%s\n' 'lake env lean Formalizacao/Auditoria.lean'
lake env lean Formalizacao/Auditoria.lean > "$evidence_dir/axiomas-auditoria.log" 2>&1
printf '%s\n' 'lake env lean ../../testes/Minimax52.lean'
lake env lean ../../testes/Minimax52.lean > "$evidence_dir/minimax52.log" 2>&1
printf '%s\n' 'lake env lean DeclaracoesF6.lean'
lake env lean "$evidence_dir/DeclaracoesF6.lean" > "$evidence_dir/declaracoes.log" 2>&1
printf '%s\n' 'lake env lean SemanticaF6.lean'
lake env lean "$evidence_dir/SemanticaF6.lean" > "$evidence_dir/semantica.log" 2>&1
cd ../..
printf '%s\n' 'python3 -B -m unittest discover -s testes -v'
python3 -B -m unittest discover -s testes -v > "$evidence_dir/unittest.log" 2>&1
printf '%s\n' 'python3 -B mapas/verificar_mapa.py'
python3 -B mapas/verificar_mapa.py > "$evidence_dir/mapa.log" 2>&1
