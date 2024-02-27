#!/usr/bin/env python3

import sys

def generate_lean_proof(depth):
    def generate_variables(current_depth, prefix='x'):
        """
        Recursively generate variable names and equations based on the current depth, with 'x' prefix.
        """
        if current_depth == 0:
            return [prefix]  # Base case: return the leaf variable
        else:
            # Generate left and right subtree variables
            left = generate_variables(current_depth - 1, prefix + '0')
            right = generate_variables(current_depth - 1, prefix + '1')
            # Generate the parent node equation
            var_left = left[-1]
            var_right = right[-1]
            equations.append(f"(_ : ({var_left} && {var_right}) = {prefix})")
            equations.append(f"({var_left} : Bool)")
            equations.append(f"({var_right} : Bool)")
            return left + right + [prefix]

    if depth < 1:
        print("Depth must be at least 1.")
        return

    global equations
    equations = []
    generate_variables(depth)

    # Add the final equation that checks if the root node (x) equals true
    equations.append("(_ : x = true)")

    # Reverse the order of equations to start from leaves to the root
    equations.reverse()

    # The proof that the first input (x followed by depth number of '0's) is true
    first_input = 'x' + '0' * depth
    proof_statement = "example " + " ".join(equations) + f" : {first_input} = true := by cnf_decide"
    print(proof_statement)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: ./script.py <depth>")
        sys.exit(1)
    try:
        depth = int(sys.argv[1])
        if depth < 1:
            raise ValueError
        generate_lean_proof(depth)
    except ValueError:
        print("Invalid depth. Depth must be a positive integer.")
        sys.exit(1)
