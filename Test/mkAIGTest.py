#!/usr/bin/env python3

import sys


def generate_lean_proof(depth):
    def generate_statement(current_depth, statement):
        while current_depth != 0:
            statement = f"({statement} && {statement})"
            current_depth -= 1
        return statement

    if depth < 1:
        print("Depth must be at least 1.")
        return
    statement = generate_statement(depth, "x")
    return f"theorem t{depth} (_ : x = true) : {statement} := by sat_decide"

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: ./script.py <depth>")
        sys.exit(1)
    try:
        depth = int(sys.argv[1])
        if depth < 1:
            raise ValueError
        print(generate_lean_proof(depth))
    except ValueError:
        print("Invalid depth. Depth must be a positive integer.")
        sys.exit(1)
