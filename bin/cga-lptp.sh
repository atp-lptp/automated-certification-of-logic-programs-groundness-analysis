#!/usr/bin/env bash
set -Eeuo pipefail

# Exécuter l'analyse de clôture,
# OU génère les dérivations à partir des invariants de clôture inférés,
# OU certifie les dérivations avec LPTP
# pour le programme passé en premier argument
# et pour le mode d'exécution passé en deuxième argument parmi les valeurs possibles :
# - 'infer_groundness_prop_with_cti'
# - 'prove_groundness_prop'
# - 'prove_groundness_prop_alt'
# - 'prove_groundness_prop_dn'
# - 'check_with_lptp_swi_prolog'
run_cga_lptp() {
  cd "${LPTP_ROOT_DIR}" || exit

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

  if [ "${execution_mode}" = 'infer_groundness_prop_with_cti_without_program' ];
  then
    cmd="${cmd}"
  fi

  if [ -n "${format_proof}" ];
  then
    export FORMAT_PROOF='FORMAT_PROOF'
  fi

  export CGA_LPTP_MODE="$(echo ${execution_mode} | sed -E 's#_without_program##g')"

  # echo -n "src/cga-lptp/cGA_LPTP ${program}" 1>&2

  echo -n "src/cga-lptp/cGA_LPTP ${program}" | \
    xargs -I{} /bin/bash -c "${cmd}" shell {} | \
    sed -E  's#^.+cGA_LPTP(.*)#\1#' | \
    sed -E  's# examples/filex/##g' | \
    sed -E  's# lib/[^/]+/##g' | \
    tr $'\n' ' ';

  unset FORMAT_PROOF
}

set +Eeuo pipefail
