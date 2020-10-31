#!/usr/bin/env python3

import unittest
import puzzle as P

class LogicTest(unittest.TestCase):
    root_group = ['1', '2', '3']
    groups = [
        ["Ruby", "Spot", "Starbuck"],
        ["laser", "sleep", "ball"],
        ["Batman", "Jake", "Dibii"]
    ]
    ex_puzzle = P.Puzzle(root_group, groups, [])

    def test_var_to_id(self):
        self.assertEqual(self.ex_puzzle.var_to_id("sleep_1"), (1, 1, 0))
        self.assertEqual(self.ex_puzzle.var_to_id("Dibii_2"), (2, 2, 1))

    def test_id_to_var(self):
        self.assertEqual(self.ex_puzzle.id_to_var((1, 1, 0)), "sleep_1")
        self.assertEqual(self.ex_puzzle.id_to_var(self.ex_puzzle.var_to_id("Dibii_2")), "Dibii_2")



if __name__ == "__main__":
  unittest.main()
