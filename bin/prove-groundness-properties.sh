#!/usr/bin/env bash
set -Eeuo pipefail

export LPTP_ROOT_DIR=${LPTP_ROOT_DIR:='../'}

#export ADD_COMPILE_GR_DIRECTIVE='true'
#export CGA_LPTP_MODE='check_with_lptp_gnu_prolog'

newline() {
  echo
}

count_lines() {
  local program
  program="${1}"

  local proof
  proof="$(echo "${program}" | sed -E 's#.pl$#_gr_formatted.pr#g')"

  echo -n "$(\cat "${proof}" | \
    grep -v 'initia\|bye\|needs\|compile\|^$' | wc -l)"
}

# Exécuter l'analyse de clôture,
# OU génère les dérivations à partir des invariants de clôture inférés,
# OU certifie les dérivations avec LPTP
# pour le programme passé en premier argument
# et pour le mode d'exécution passé en deuxième argument parmi les valeurs possibles :
# - 'infer_groundness_prop_with_cti'
# - 'prove_groundness_prop'
# - 'check_with_lptp_swi_prolog'
run_cga_lptp() {
  local program
  program="${1}"

  local execution_mode
  execution_mode="${2}"

  local format_proof
  format_proof="${3:-}"

  local exclusion_pattern
  exclusion_pattern='"Version\|Copyright"'

  local output_result
  output_result='| grep -v '"${exclusion_pattern}"

  local cmd
  cmd='${1} 2>&1 '"${output_result}"

  if [ "${execution_mode}" = 'infer_groundness_prop_with_cti' ];
  then
    cmd='echo -n "${1} "'"'&'"'" " && '"${cmd}"
  fi

  if [ -n "${format_proof}" ];
  then
    export FORMAT_PROOF='FORMAT_PROOF'
  fi

  export CGA_LPTP_MODE="${execution_mode}"

  echo -n "src/cga-lptp/cGA_LPTP ${program}" | \
    xargs -I{} /bin/bash -c "${cmd}" shell {} | \
    sed -E  's#^.+cGA_LPTP(.*)#\1#' | \
    sed -E  's# examples/filex/##g' | \
    sed -E  's# lib/[^/]+/##g' | \
    tr $'\n' ' ';

  unset FORMAT_PROOF
}

include_exclude_from_input() {
  local pattern
  pattern='inorder.pl\|sequence.pl\|elem.pl\|loop.pl\|lex.pl\|test.pl\|testneg.pl\|tiny.pl\|ex30.pl\|expmr.pl\|extrait_peep.pl\|mini.pl\|mr.pl\|pi.pl\|pq.pl'

  local exclude_program_filter
  exclude_program_filter='builtin\|gcd\|inorder.pl\|sequence.pl'

  if [ -n "${INTER_ARGS}" ];
  then
    \cat - | grep "${pattern}" | grep -v "${exclude_program_filter}"
  else
    \cat - | grep -v "${pattern}\|${exclude_program_filter}"
  fi

  unset INTER_ARGS
}

# Exécuter l'analyse de clôture,
# génère les dérivations à partir des invariants de clôture inférés,
# et certifie les dérivations avec LPTP
# pour les programmes dans les dossiers examples/filex et lib.
run_analysis_derivation_certification() {
  local inter_argument_relations_only
  inter_argument_relations_only="${1:-}"

  if [ -n "${inter_argument_relations_only}" ];
  then
    export INTER_ARGS=1
  else
    export INTER_ARGS=''
  fi

  ( cd "${LPTP_ROOT_DIR}" || exit
  for program in $(\ls -1 examples/filex/*pl lib/*/*pl | include_exclude_from_input); do

    run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' && echo -n ' & '

    if [ -z "${inter_argument_relations_only}" ];
    then

      run_cga_lptp "${program}" 'prove_groundness_prop' && echo -n ' & '
      run_cga_lptp "${program}" 'check_with_lptp_swi_prolog' && echo -n ' & '
      ## Décommenter afin de formater les dérivations avant de compter ses lignes
      # run_cga_lptp "${program}" 'prove_groundness_prop' 'format_proof' && echo -n ' & '
      count_lines "${program}"

      echo -n '\\'

    else

      echo -n '& & \\'

    fi
    newline

  done 2>&1 )
}

remove_latex_characters() {
  if [ -n "${LATEX:-}" ];
  then
    cat -  | \
    sed -E 's#_#\\_#g'
  else
    cat - | \
    sed -E 's#\s*\&\s*#\t#g' | \
    sed -E 's#\s*\&\s*#\t#g' | \
    sed -E 's#\\\\##g' | \
    sed -E 's#\n\n##g' | \
    sed -E 's#\\hline##g'
  fi
}

run_benchmark() {
  (
    echo 'Prog. & Prop. & Vars & Inf. (ms) & Deriv. (ms) &  Cert. (ms) & LOC'

    if [ -n "${LATEX:-}" ];
    then
      echo '\\'
      echo '\hline'
    fi

    run_analysis_derivation_certification
    run_analysis_derivation_certification inter_argument_relations_only
  ) 2>&1 | \
  remove_latex_characters | \
  tee ./../tmp/benchmark_results.txt
}
run_benchmark

set +Eeuo pipefail
