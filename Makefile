SHELL := bash
.PHONY: deps build check ci offline-audit clean

# Standard public path: resolve Mathlib v4.33.0 and download its cache once.
deps:
	lake update
	lake exe cache get

build: deps
	lake build

# Python/axiom/claims/reproduction checks; requires a completed `lake build`.
check: build
	bash scripts/ci_check.sh

ci: deps build check

# Author offline audit: requires prebuilt Mathlib packages and ELAN_HOME.
# Not used by public CI.
offline-audit:
	bash scripts/verify_all.sh

clean:
	rm -rf lean/build logs/build vendor/CausModel/.lake
