#!/usr/bin/env bash
set -Eeuo pipefail

function install_lptp() {
    ( cd src && make clean && make lptp && gplc --global-size 32768 -o ./lptp ./lptp.pl  && mv ./lptp ../bin  )
}
alias install-lptp='install_lptp'

set +Eeuo pipefail

