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

from pyeda.inter import And, Or, OneHot, exprvars, expr2truthtable, espresso_exprs
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
        Gets the list indices of the non-root group value given as a tuple
        :param value: str- name of a value in one of the puzzle categories
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

    def only_one_root(self):
        """
        Returns the formula where every group value can only belong to one root value
        in dnf form
        """
        form = []
        for group in range(0, self.items_per):
            f = And(*[
                OneHot(*[ self.X[group, idx, root]
                    for root in range(0, self.items_per) ])
                for idx in range(0, self.items_per) ])
            form.append(f.to_dnf())

        f_onlyoneroot = And(*[f for f in form])

        return f_onlyoneroot.to_dnf()

    def one_in_each(self):
        """
        Returns the formula where every value in a group must belong to different root values
        in dnf form
        """
        form = []
        for group in range(0, self.items_per):
            f = And(*[
                OneHot(*[ self.X[group, idx, root]
                    for idx in range(0, self.items_per) ])
                for root in range(0, self.items_per) ])
            form.append(f.to_dnf())

        f_oneineach = And(*[f for f in form])

        return f_oneineach.to_dnf()

    def are_same(self, value1, value2):
        """
        Returns the formula where the two given (non-root) values are a match-- they occur at the same root value
        """
        (group_1, val_1) = self.get_val_tuple(value1)
        (group_2, val_2) = self.get_val_tuple(value2)
        f_aresame = Or(*[ And(self.X[group_1, val_1, idx], self.X[group_2, val_2, idx])
                        for idx in range(0, self.items_per) ])

        return f_aresame

    def are_not(self, value1, value2):
        """
        Returns the formula where the two given (non-root) values are a not-- they do not occur at the same root value
        """
        (group_1, val_1) = self.get_val_tuple(value1)
        (group_2, val_2) = self.get_val_tuple(value2)
        f_arenot = Or(*[ And(self.X[group_1, val_1, idx], ~self.X[group_2, val_2, idx])
                        for idx in range(0, self.items_per) ])

        return f_arenot

    def is_at(self, value, root_val):
        """
        Returns the formula where the given non root value is at the given root value
        :param value: str- the non root value that matches with the root value
        :param root_val: str- the root value that matches with the given category value
        """
        (group, val) = self.get_val_tuple(value)
        idx = self.root_group.index(root_val)
        return self.X[group, val, idx]

    def is_not_at(self, value, root_val):
        """
        Returns the formula where the given non root value is not at the given root value
        :param value: str- the non root value that does not match with the root value
        :param root_val: str- the root value that does not match with the given category value
        """
        (group, val) = self.get_val_tuple(value)
        idx = self.root_group.index(root_val)
        return ~self.X[group, val, idx]


    def is_x_away(self, val1, val2, steps):
        """
        Returns the formula for the comparison clue where val1 is some number of value steps away from val2,
        where the comparison factor is the root group, and val2 must be at one of the root values that makes
        such an implication possible. in dnf form
        :param steps: int- can be positive or negative where val1 + steps = val2 in terms of number of values away
                      eg. for values [$2, $4, $6], $2 more is 1 step, $4 is 2 steps.
        :param val1: str- one of the non root values being compared
        :param val2: str- one of the non root values being compared
        """
        (group_1, v_1) = self.get_val_tuple(val1)
        (group_2, v_2) = self.get_val_tuple(val2)
        f_away = []
        for curr in range(0, self.items_per):
            if (curr - steps >= 0):
                f_away.append(And(self.X[group_2, v_2, curr], self.X[group_1, v_1, curr - steps]))

        f_away = OneHot(*[f for f in f_away ])
        return f_away.to_dnf()

    def dnf_formula(self):
        form = And(*[f for f in self.formula ])
        esp_form, = espresso_exprs(form.to_dnf())
        return esp_form

    def fid_to_id(self, fid):
        """
        Translate expr formula id to id as a list of integers representing that indices of that variable
        :param fid: str- the given expr formula id in the format 'x[a,b,c]'
        """
        as_str = str(fid)[2:7].split(',')
        return [int(i) for i in as_str]

    def solve(self):
        form = And(*[f for f in self.formula ])
        solved = form.satisfy_one()
        sol = [self.fid_to_id(var) for var in list(solved.keys()) if solved[var] == 1]
        sol = [self.id_to_var(id)  for id in sol]
        sol.sort(key = lambda var: int(var[-1:]))
        print(form.satisfy_count())

        return sol

        # number of solutions
        # print(form.satisfy_count())
        # print("\n\nSOLVED\n")
        # print(test)


    def run(self):
        self.formula.append(self.only_one_root())
        self.formula.append(self.one_in_each())
        self.formula.append(self.are_same("Batman", "ball"))
        self.formula.append(self.are_not("ball", "Starbuck"))
        self.formula.append(self.are_same("Dibii", "laser"))
        self.formula.append(self.are_same("Ruby", "sleep"))
        self.formula.append(self.is_x_away("Batman", "Starbuck", 2))
        # self.dnf_formula()
        print(self.solve())
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