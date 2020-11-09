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
    clues = [
        {
            "type": "SAME",
            "vals": ["Batman", "ball"]
        },
        {
            "type": "XAWAY",
            "vals": ["Batman", "Starbuck", 2]
        },
        {
            "type": "SAME",
            "vals": ["Dibii", "laser"]
        }
    ]
    ex_puzzle = P.Puzzle(root_group, groups, clues)

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

    def test_get_same_mapping(self):
        sames = {
            "Batman": "ball",
            "ball": "Batman",
            "Dibii": "laser",
            "laser": "Dibii"
        }
        self.assertEqual(self.ex_puzzle.get_same_mapping(), sames)

    def test_new_clue(self):
        sames = self.ex_puzzle.get_same_mapping()
        clue = {
            "type": "XAWAY",
            "vals": ["Batman", "laser", 1]
        }
        new_clue = {
            "type": "XAWAY",
            "vals": ["ball", "Dibii", 1]
        }
        clue_nomatch = {
            "type": "XAWAY",
            "vals": ["Ruby", "sleep", -1]
        }
        clue_not = {
            "type": "NOTSAME",
            "vals": ["ball", "Dibii"]
        }
        new_clue_not = {
            "type": "NOTSAME",
            "vals": ["Batman", "laser"]
        }

        self.assertEqual(self.ex_puzzle.new_clue(sames, clue), new_clue)
        self.assertEqual(self.ex_puzzle.new_clue(sames, clue_not), new_clue_not)
        self.assertFalse(self.ex_puzzle.new_clue(sames, clue_nomatch))

    def test_alt_clueset(self):
        alt =[
            {
                "type": "SAME",
                "vals": ["Batman", "ball"]
            },
            {
                "type": "XAWAY",
                "vals": ["ball", "Starbuck", 2]
            },
            {
                "type": "SAME",
                "vals": ["Dibii", "laser"]
            }
        ]
        self.assertEqual(self.ex_puzzle.alt_clueset(), alt)

        no_puzzle = P.Puzzle([], [], [])
        self.assertFalse(no_puzzle.alt_clueset())

    def test_only_one_root(self):
        small_puzzle = P.Puzzle(["1", "2"], [["a", "b"]], [])
        sx = small_puzzle.X
        root_rule_form = (And( Or( And(sx[0,0,0], ~sx[0,0,1]), And(~sx[0,0,0], sx[0,0,1])),
        Or( And(sx[0,1,0], ~sx[0,1,1]), And(~sx[0,1,0], sx[0,1,1]))))

        self.assertTrue(And(*small_puzzle.only_one_root()).equivalent(root_rule_form))

    def test_eval_clue(self):
        clue = {
            "type": "ISAT",
            "vals": ["laser", "1"]
        }
        self.assertTrue(self.ex_puzzle.eval_clue(clue).equivalent(self.ex_puzzle.X[1, 0, 0]))
        self.assertRaises(Exception, self.ex_puzzle.eval_clue, { "type": "asd" })


if __name__ == "__main__":
  unittest.main()
