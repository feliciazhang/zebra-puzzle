"""
Approach based on Raymond Hettinger's Einstein puzzle solution:
https://rhettinger.github.io/einstein.html#code-for-the-einstein-puzzle
"""

from pyeda.inter import And, Or, OneHot, exprvars, espresso_exprs
from pprint import pprint
import json
import re
import sys

SAME = 'SAME'
NOTSAME = 'NOTSAME'
XAWAY = 'XAWAY'
ISAT = 'ISAT'
NOTAT = 'NOTAT'

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
        return form

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
        return form

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
            if (curr - steps >= 0 and curr - steps < self.items_per):
                f_away.append(And(self.X[group_2, v_2, curr], self.X[group_1, v_1, curr - steps]))

        f_away = OneHot(*[f for f in f_away ])
        return f_away.to_dnf()
        
    def eval_espresso(self):
        """
        Minimize this puzzle's formula using espresso
        """
        form = And(*[f.to_dnf() for f in self.formula ])
        esp_form, = espresso_exprs(form.to_dnf())
        return esp_form

    def fid_to_var(self, fid):
        """
        Translate expr formula id to its corresponding english variable
        :param fid: str- the given expr formula id in the format 'x[a,b,c]'
        """
        index_only = fid[2:7].split(',')
        id = [int(i) for i in index_only]
        x, y, z = id
        value = self.groups[x][y]
        root = self.root_group[z]
        return f'{value}_{root}'

    def solve(self):
        form = And(*[f for f in self.formula ])
        solved = form.satisfy_one()
        sol = [self.fid_to_var(str(var)) for var in list(solved.keys()) if solved[var] == 1]
        sol.sort(key = lambda var: var.split('_')[-1])
        print("Total possible solutions: ")
        print(form.satisfy_count())

        print("SOLUTION: ")
        return sol

    def eval_clues(self, clue):
        """
        Returns the boolean formula for the given clue based on its type and values
        :param clue: dict- a clue in the format of a proper JSON Clue
        """
        clue_type = clue["type"]
        clue_args = clue["vals"]
        if (clue_type == SAME):
            return self.are_same(clue_args[0], clue_args[1])
        elif (clue_type == NOTSAME):
            return self.are_not(clue_args[0], clue_args[1])
        elif (clue_type == XAWAY):
            return self.is_x_away(clue_args[0], clue_args[1], clue_args[2])
        elif (clue_type == ISAT):
            return self.is_at(clue_args[0], clue_args[1])
        elif (clue_type == NOTAT):
            return self.is_not_at(clue_args[0], clue_args[1])
        else:
            return None

    def big_base_dnf(self):
        """
        Gets the two formulas that represent the basic rules of having exactly one value per category match with each other
        and appends those two formulae And'd together in dnf form to this puzzle's formula. This must be done in merged stages
        because it is too big of a formula to turn to dnf all at once.
        """
        base = self.only_one_root() + self.one_in_each()
        group_by = 4
        while len(base) > 1:
            base_help = []
            for i in range(0, len(base), group_by):
                form = And(*[f for f in base[i: i+group_by] ])
                base_help.append(form.to_dnf())
            base = base_help

        self.formula.append(base[0])

    def translate_f(self, formula):
        """
        Translates a formula into english variable names
        :param formula: Expr- the formula
        """
        eng_formula = re.sub('x\[\d,\d,\d\]', lambda match: self.fid_to_var(match.group()), str(formula))
        return eng_formula

    def run(self):
        self.big_base_dnf()

        for clue in self.clueset:
            f = self.eval_clues(clue)
            if f:
                self.formula.append(f)
        print(self.solve())

        print("\n\nMinimized formula: ")
        print(self.translate_f(self.eval_espresso()))

        #no pprint(expr2truthtable(f_aresame))


def clean_input(input):
    """
    Returns std input read from the command line as a pythonized JSON object. Input is valid JSON.
    """
    lines = list(map(lambda item: item.strip(), input))
    lines = list(filter(None, lines))
    lines_as_string = "".join(lines)
    return json.loads(lines_as_string)

def main():
    params = clean_input(sys.stdin.readlines())
    print(params["description"])
    puz = Puzzle(params["root"], params["groups"], params["clues"])
    puz.run()

if __name__ == "__main__":
  main()
