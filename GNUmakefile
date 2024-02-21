# Ensure that panics actually cause the tests to fail
export LEAN_ABORT_ON_PANIC=1

.PHONY: all build test lint

all: build test

build:
	lake build

test:
	lake build Test

%.run: build
	lake env lean $(@:.run=.lean)

lint: build
	lake exe runLinter Sat
