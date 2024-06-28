#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
This module generates (maybe) worst-case lambda expressions.
"""

import sys

def print_worst_case(n):
    # Print the initial part of the lambda expression
    print("\\k. ", end="")

    # Print each variable declaration
    for i in range(n):
        print(f"\\x{i}. ", end="")

    # Print the function application part
    print("k ", end="")
    for i in range(n):
        print(f"x{i} ", end="")

    # Finish the line
    print()

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: worstcase.py <number>")
        sys.exit(1)

    try:
        n = int(sys.argv[1])
    except ValueError:
        print("Please provide an integer.")
        sys.exit(1)

    print_worst_case(n)
