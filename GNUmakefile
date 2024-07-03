# Ensure that panics actually cause the tests to fail
export LEAN_ABORT_ON_PANIC=1

.PHONY: all build test eval

all: build test

build:
	lake build

test:
	lake test

eval:
	bash check_eval.bash
