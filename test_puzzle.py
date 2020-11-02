#!/usr/bin/env python3

import unittest
import puzzle as P
from pyeda.inter import And, OneHot, Or

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

    def test_fid_to_var(self):
        self.assertEqual(self.ex_puzzle.fid_to_var('x[1,1,0]'), "sleep_1")

    def test_get_val_tuple(self):
        self.assertEqual(self.ex_puzzle.get_val_tuple("sleep"), (1, 1))

    def test_is_at(self):
        self.assertEqual(self.ex_puzzle.is_at("laser", "1"), self.ex_puzzle.X[1, 0, 0])

    def test_is_not_at(self):
        self.assertEqual(self.ex_puzzle.is_not_at("laser", "1"), ~self.ex_puzzle.X[1, 0, 0])

    def test_is_x_away(self):
        away2 = And(self.ex_puzzle.X[0,2,2], self.ex_puzzle.X[2,0,0])
        away1 = (OneHot(And(self.ex_puzzle.X[0,2,2], self.ex_puzzle.X[2,0,1]),
        And(self.ex_puzzle.X[0,2,1], self.ex_puzzle.X[2,0,0])))
        away_neg = And(self.ex_puzzle.X[0,2,2], self.ex_puzzle.X[2,0,0])

        self.assertTrue(self.ex_puzzle.is_x_away("Batman", "Starbuck", 2).equivalent(away2))
        self.assertTrue(self.ex_puzzle.is_x_away("Batman", "Starbuck", 1).equivalent(away1))
        self.assertTrue(self.ex_puzzle.is_x_away("Starbuck", "Batman", -2).equivalent(away_neg))

    def test_translate_f(self):
        f = (Or(And(self.ex_puzzle.X[0,2,2], self.ex_puzzle.X[2,0,1]),
        And(self.ex_puzzle.X[0,2,1], self.ex_puzzle.X[2,0,0])))
        f_str = 'Or(And(Starbuck_3, Batman_2), And(Starbuck_2, Batman_1))'

        self.assertEqual(self.ex_puzzle.translate_f(f), f_str)


if __name__ == "__main__":
  unittest.main()
