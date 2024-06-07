#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
This module generates Church numerals.
"""

import sys

def print_church_numeral(n):
    # Print the initial part of the lambda expression
    print("\\f. \\x. ", end="")

    # Print each 'f(' n times before the 'x'
    for _ in range(n):
        print("f(", end="")

    # Print the base variable
    print("x", end="")

    # Print ')' n times after the 'x'
    for _ in range(n):
        print(")", end="")

    # Ensure everything is output
    print()

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: church.py <number>")
        sys.exit(1)

    try:
        n = int(sys.argv[1])
    except ValueError:
        print("Please provide an integer.")
        sys.exit(1)

    print_church_numeral(n)
