"""
Approach based on Raymond Hettinger's Einstein puzzle solution:
https://rhettinger.github.io/einstein.html#code-for-the-einstein-puzzle

Easy logic puzzle- Cats in Spring
https://www.ahapuzzles.com/logic/logic-puzzles/cats-in-spring/

Categories:
*# Kittens      ['1', '2', '3']
Female          ["Ruby", "Spot", "Starbuck"]
Activity        ["laser", "sleep", "ball"]
Male            ["Batman", "Jake", "Dibii"]

* root category

Clues:
1. Batman chose the female who liked to chase a ball, but she was not Starbuck.
2. Dibii's companion liked to chase the laser light.
3. Ruby loved to cuddle up to her male for a long afternoon nap in the sun.
4. Starbuck had two more kittens than Batman's companion.
"""

from pyeda.inter import *
from pprint import pprint

class Puzzle:
    root_group = []
    groups = []
    clueset = []
    items_per = 0
    formula = []
    X = None


    def __init__(self, root_group, groups, clueset):
        self.items_per = len(root_group)
        self.root_group = root_group
        self.groups = groups
        self.clueset = clueset


        self.X = exprvars('x', (0, self.items_per), (0, self.items_per), (0, self.items_per))

    def id_to_var(self, id):
        """
        Translates the id tuple (x, y, z) into the english variable, where x,y referes to the indices
        of the 2D groups list, and z is the index of the root category
        """
        x, y, z = id
        value = self.groups[x][y]
        root = self.root_group[z]
        return f'{value}_{root}'

    def get_val_tuple(self, value):
        """
        Gets the x,y list index of the group value given
        """
        group_id = ([(idx1, idx2)
                    for idx1, category in enumerate(self.groups)
                        for idx2, val in enumerate(category) if val == value])
        return group_id[0]

    def var_to_id(self, var):
        """
        Translates and English variable in the 'value_root' form to an id tuple (x, y, z),
        where x,y referes to the indices of the 2D groups list, and z is the index of the root category
        """
        var_split = var.split("_")
        root_idx = self.root_group.index(var_split[1])
        group_id = self.get_val_tuple(var_split[0])

        return (group_id[0], group_id[1], root_idx)

    def one_in_each(self):
        """
        Returns the formula where only one item of each category can belong to the same root value
        """
        f_oneineach = And(*[
                        And(*[
                            OneHot(*[ self.X[group, idx, root]
                                for root in range(0, self.items_per) ])
                            for idx in range(0, self.items_per) ])
                        for group in range(0, self.items_per) ])


        print(f_oneineach)
        # print("\n\n")

        # f_dnf = f_oneineach.to_dnf()
        # print(f_dnf)
        # f1m = espresso_exprs(f_dnf)
        # print("\n\n")
        # print(f1m)
        # print("\n\n")
        # print(f_oneineach)

        return f_oneineach

    def are_same(self, value1, value2):
        """
        Returns the formula where the two given (non-root) values are a match-- they occur at the same root value
        """
        (group_1, val_1) = self.get_val_tuple(value1)
        (group_2, val_2) = self.get_val_tuple(value2)
        f_aresame = Or(*[ And(self.X[group_1, val_1, idx], self.X[group_2, val_2, idx])
                        for idx in range(0, self.items_per) ])


        # print(f_aresame)
        return f_aresame

    def are_not(self, value1, value2):
        """
        Returns the formula where the two given (non-root) values are a not-- they do not occur at the same root value
        """
        (group_1, val_1) = self.get_val_tuple(value1)
        (group_2, val_2) = self.get_val_tuple(value2)
        f_arenot = Or(*[ And(self.X[group_1, val_1, idx], ~self.X[group_2, val_2, idx])
                        for idx in range(0, self.items_per) ])


        # print(f_arenot)
        return f_arenot

    def is_x_away(self, val1, val2, steps, group_id):
        """
        Returns the formula for the comparison clue where val1 is some number of value steps away from val2.
        steps (int): can be positive (older, larger, greater than etc) or negative (younger, earlier, less than etc) where val1 + steps = val2
                     in terms of number of values away-- for values [$2, $4, $6], $2 more is 1 step, $4 is 2 steps.
        group_id (int): the index of the category that the steps refers to
        """

    def dnf_formula(self):
        form = And(*[f for f in self.formula ])
        # Messing around w solving
        # test = form.satisfy_all()
        # # number of solutions
        # print(sum(1 for dummy in test))
        # print("\n\nSOLVED\n")
        # print(test)
        # esp_form, = espresso_exprs(form.to_dnf())
        # print(esp_form)


    def run(self):
        self.formula.append(self.one_in_each())
        self.formula.append(self.are_same("Batman", "ball"))
        self.formula.append(self.are_not("ball", "Starbuck"))
        self.formula.append(self.are_same("Dibii", "laser"))
        self.formula.append(self.are_same("Ruby", "sleep"))
        self.dnf_formula()
        # pprint(expr2truthtable(f_aresame))




root_group = ['1', '2', '3']
groups = [
    ["Ruby", "Spot", "Starbuck"],
    ["laser", "sleep", "ball"],
    ["Batman", "Jake", "Dibii"]
]

ex_puzzle = Puzzle(root_group, groups, [])
ex_puzzle.run()



"""
read input file from cmd,
w clues in a standardized parseable format (or use expected json messages)
"""
