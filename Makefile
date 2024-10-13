SHELL:=/bin/bash

.PHONY: \
	lptp-swi \
	test-swi-prolog \
	run-groundness-analysis-tests \
	run-benchmark \
	run-benchmark-latex

help:
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

lptp-swi: ## Build LPTP binary by calling qcompile after assembling all source files into src/lptp.pl
	@sh -c "( cd src && make lptp ) && swipl -s ./src/lptp.pl -g 'qcompile(\"src/lptp.pl\").' -t halt"

test-swi-prolog: ## Run tests passing with SWI Prolog
	@bash -c "( cd src && swipl -s './lptp.qlf' -g 'consult('all').' )"

run-groundness-analysis-tests: lptp-swi ## Run groundness analysis tests
	@swipl -s './src/test/groundness_analysis_test.pl' -g 'run_tests.' -t halt

run-benchmark: lptp-swi ## Run benchmark
	bash -c 'cd ./bin && . prove-groundness-properties.sh'

run-benchmark-latex: lptp-swi ## Run benchmark
	bash -c 'cd ./bin && export LATEX=1 && . prove-groundness-properties.sh'
