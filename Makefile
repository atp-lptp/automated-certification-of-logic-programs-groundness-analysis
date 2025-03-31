SHELL:=/bin/bash

SUFFIX_E_PROVER ?= "_e_prover"
SUFFIX_VAMPIRE ?= "_vampire"

# Apply both Vampire system and E Theorem Prover in parallel
MAKEFLAGS += -j2

.PHONY: \
	lptp-swi \
	test-swi-prolog \
	run-groundness-analysis-tests \
	run-benchmark \
	run-benchmark-latex \
	run-prover-alt

help:
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

lptp-swi: ## Build LPTP binary by calling qcompile after assembling all source files into src/lptp.pl
	@sh -c "( cd src && make lptp ) && swipl -s ./src/lptp.pl -g 'qcompile(\"src/lptp.pl\").' -t halt"

test-swi-prolog: ## Run tests passing with SWI Prolog
	@bash -c "( cd src && swipl -s './lptp.qlf' -g 'consult('all').' )"

run-groundness-analysis-tests: lptp-swi ## Run groundness analysis tests
	@swipl -s './src/test/groundness_analysis_test.pl' -g 'run_tests.' -t halt

run-benchmark: lptp-swi ## Run benchmark
	@bash -c 'cd ./bin && . prove-groundness-properties.sh'

run-benchmark-latex: lptp-swi ## Run benchmark
	@bash -c 'cd ./bin && export LATEX=1 && . prove-groundness-properties.sh'

run-prover-alt: lptp-swi ## Run alternative prover
	@bash -c 'cd ./bin && . ./cga-lptp.sh && run_cga_lptp "$$LOGIC_PROGRAM" "$$EXECUTION_MODE"  "$$FORMAT_PROOF"'

test-prove-alt: lptp-swi ### Run prover tests
	swipl -g run_tests -s ./src/prover/prover_alt_test.pl -g halt.

test-prove-dslplm-alt: lptp-swi ### Run Devismes Lafourcade Levy prover tests
	swipl -g run_tests -s ./src/prover/prover_dslplm_test.pl -g halt.

test-nat: ### Run nat test
	@export EXECUTION_MODE=prove_groundness_prop_alt \
	FORMAT_PROOF=1 \
	LOGIC_PROGRAM=lib/nat/nat.pl \
	LPTP_ROOT_DIR=../ && make run-prover-alt

test-addmul: ### Run addmul test
	@export EXECUTION_MODE=prove_groundness_prop_alt \
	FORMAT_PROOF=1 \
	LOGIC_PROGRAM=examples/filex/addmul.pl \
	LPTP_ROOT_DIR=../ && make run-prover-alt

test-fib: ### Run fib test
	@export EXECUTION_MODE=prove_groundness_prop_alt \
	FORMAT_PROOF=1 \
	LOGIC_PROGRAM=examples/filex/fib.pl \
	LPTP_ROOT_DIR=../ && make run-prover-alt

test-all: test-addmul test-fib test-nat


### START ---- Proving properties with Vampire and E Theorem Prover

build:
### Build .fof,.pl,.pr files for logic program exported as LOGIC_PROGRAM environment variable
	@. ./bin/build.sh && \
	build "$${LOGIC_PROGRAM}"

build-fof: ### Build .fof files (conjectures and axioms in first-order form) for logic program exported as LOGIC_PROGRAM environment variable
	@. ./bin/start.sh && \
	build_fof "$${LOGIC_PROGRAM}"

build-requirements-for-each-program:
### Build .fof,.pl,.pr files for all logic programs available in ./src
	@. ./bin/build.sh && \
	build_all

check-requirements:
### Check if requirements are satisfied
	@. ./bin/check.sh && \
	check_requirements "$${LOGIC_PROGRAM}"

apply-e-theorem-prover: check-requirements
### Apply E Theorem Prover to conjectures and axioms in first-order form
	@export \
	PROVER_CMD_TPL="time $$(which eprover)"' --auto --cpu-limit=_TIMEOUT_ -s ' \
	OUTPUT_SUFFIX="${SUFFIX_E_PROVER}" && \
	. ./bin/start.sh && \
	apply_prover_with_predefined_time_limits "$${PROVER_CMD_TPL}" "$${OUTPUT_SUFFIX}" "$${LOGIC_PROGRAM}"

apply-vampire: check-requirements
### Apply Vampire system to conjectures and axioms in first-order form
	@export \
	PROVER_CMD_TPL="time $$(which vampire)"' --proof off ' \
	OUTPUT_SUFFIX="${SUFFIX_VAMPIRE}" && \
	. ./bin/start.sh && \
	apply_prover_with_predefined_time_limits "$${PROVER_CMD_TPL}" "$${OUTPUT_SUFFIX}" "$${LOGIC_PROGRAM}"

start: apply-vampire apply-e-theorem-prover ### Apply both Vampire system and E Theorem Prover to conjectures and axioms in first-order form

apply-provers: apply-vampire apply-e-theorem-prover

apply-provers-for-each-program:
### Apply both Vampire system and E Theorem Prover to conjectures and axioms in first-order form for each program in ./src
	. ./bin/start.sh && \
	apply_prover_for_each_program_with_predefined_time_limits

results:
### Parse results in ./out for "${LOGIC_PROGRAM}" exported as environment variable
	@export \
 	SUFFIX_E_PROVER="${SUFFIX_E_PROVER}" \
 	SUFFIX_VAMPIRE="${SUFFIX_VAMPIRE}" && \
	. ./bin/parse_results.sh && \
	print_results_header && \
	join_parsed_results_for_predefined_time_limits "$${LOGIC_PROGRAM}"

results-for-each-program:
### Parse all results in ./out
	@export \
 	SUFFIX_E_PROVER="${SUFFIX_E_PROVER}" \
 	SUFFIX_VAMPIRE="${SUFFIX_VAMPIRE}" && \
	. ./bin/parse_results.sh && \
	list_all_results

all-results: results-for-each-program

all-results-in-latex:
### Parse all results in ./out before rendering them in LaTeX format
	@export \
 	SUFFIX_E_PROVER="${SUFFIX_E_PROVER}" \
 	SUFFIX_VAMPIRE="${SUFFIX_VAMPIRE}" && \
	. ./bin/parse_results.sh && \
	list_all_results_latex

### END ---- Proving properties with Vampire and E Theorem Prover
