#!/usr/bin/env bash
set -Eeuo pipefail

. './cga-lptp.sh'

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


include_exclude_from_input() {
  local pattern
  pattern='inorder.pl\|sequence.pl\|elem.pl\|loop.pl\|lex.pl\|test.pl\|testneg.pl\|tiny.pl\|ex30.pl\|expmr.pl\|extrait_peep.pl\|mini.pl\|mr.pl\|pi.pl\|pq.pl'

  local exclude_program_filter
  exclude_program_filter='builtin\|gcd\|inorder.pl\|sequence.pl\|micgram.pl'

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

  local i

  if [ -n "${inter_argument_relations_only}" ];
  then
    export INTER_ARGS=1
  else
    export INTER_ARGS=''
  fi

  ( cd "${LPTP_ROOT_DIR}" || exit
  for program in $(\ls -1 examples/filex/*pl lib/*/*pl | include_exclude_from_input); do

#    echo "${program}" 1>&2

    printf '%s ' "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' | awk '{print $1}')";
    printf '%s ' "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' | awk '{print $2}')";
    printf '%s ' "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' | awk '{print $3}')";
    printf '%s ' "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' | awk '{print $4}')";
    printf '%s ' "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' | awk '{print $5}')";
    printf '%s ' "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' | awk '{print $6}')";
    printf '%.0f & ' "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti' | awk '{print $7}')";

    # There is no much difference when comparing 5 distinct inference runs
    #    printf '%.0f' "$(echo "($(for i in $(seq 1 5) ; \
    #      do echo "$(run_cga_lptp "${program}" 'infer_groundness_prop_with_cti')+";
    #    done)0)/5" | bc)" && echo -n ' & '

    if [ -z "${inter_argument_relations_only}" ];
    then

      ## Dé-commenter afin d'obtenir les dérivations à partir de l'algorithme de Huth & Ryan
      printf '%.0f ' "$(run_cga_lptp "${program}" 'prove_groundness_prop' | sed -E 's# ##g')" && echo -n ' & '

      ## [Dé-]commenter afin d'obtenir les dérivations de complexité moins élevée
      #run_cga_lptp "${program}" 'prove_groundness_prop' && echo -n ' & '

      printf '%.0f ' "$(run_cga_lptp "${program}" 'check_with_lptp_swi_prolog' | sed -E 's# ##g')" && echo -n ' & '

      ## Dé-commenter afin de formater les dérivations avant de compter ses lignes
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
#  remove_latex_characters | \
  tee ./../tmp/benchmark_results.txt
}
run_benchmark

set +Eeuo pipefail
