from pyeda.inter import And, Or, OneHot, exprvars, espresso_exprs
from pprint import pprint
import re

SAME = 'SAME'
NOTSAME = 'NOTSAME'
XAWAY = 'XAWAY'
ISAT = 'ISAT'
NOTAT = 'NOTAT'


"""
The Puzzle class serves as a representation of a logic grid puzzle and has functions to perform
various logical computations on the puzzle, including minimizing the formula, determining redundant
clues, and creating equivalent alternate clues.

Representation of a logic puzzle:
X - a multidimensional list of variables that are pyeda expressions, representing the puzzle variables.
    Each variable is in the format of 'value_root' in english, meaning that value belongs with this root value.
    Variables in X are identified by 3 indices X[x,y,z] where (x,y) refers to a value in the list of groups (2d list),
    and z is the index of the root value associated.
root_group List<str> - one of the puzzle categories, normally chosen as the one with comparable (eg numerical) values
groups List<List<str>> - the other puzzle categories
clueset List<Clue> - all puzzle clues, formatted as described in README
"""
class Puzzle:
    root_group = []
    groups = []
    clueset = []
    X = None
    items_per = 0
    formula = []

    def __init__(self, root_group, groups, clueset):
        self.items_per = len(root_group)
        self.root_group = root_group
        self.groups = groups
        self.clueset = clueset

        self.X = exprvars('x', (0, len(self.groups)), (0, self.items_per), (0, self.items_per))

    def get_val_tuple(self, value):
        """
        Gets the list indices of the non-root group value given as a tuple
        :param value: str- name of a value in one of the puzzle categories
        :return Tuple<int, int>: where the two indices represent the coordinates of the given value in self.groups
        """
        group_id = ([(idx1, idx2)
                    for idx1, category in enumerate(self.groups)
                        for idx2, val in enumerate(category) if val == value])
        return group_id[0]

    def var_to_id(self, var):
        """
        Translates and English variable in the 'value_root' form to an id tuple (x, y, z),
        where x,y referes to the indices of the 2D groups list, and z is the index of the root category
        :param var: str- an English variable name to translate
        :return Tuple<int, int, int>: the indices for the variable in expression form
        """
        var_split = var.split("_")
        root_idx = self.root_group.index(var_split[1])
        group_id = self.get_val_tuple(var_split[0])

        return (group_id[0], group_id[1], root_idx)

    def fid_to_var(self, fid):
        """
        Translate expr formula id to its corresponding english variable
        :param fid: str- the given expr formula id in the format 'x[a,b,c]'
        :return str: the English name for the expression variable in the form "var_root"
        """
        index_only = fid[2:7].split(',')
        id = [int(i) for i in index_only]
        x, y, z = id
        value = self.groups[x][y]
        root = self.root_group[z]
        return f'{value}_{root}'

    def only_one_root(self):
        """
        Gets the formula where every group value can only belong to one root value
        :return List<Expr>: a list of subformulae that when Anded together creates the formula for this rule
        """
        form = []
        for group in range(0, len(self.groups)):
            f = And(*[
                OneHot(*[ self.X[group, idx, root]
                    for root in range(0, self.items_per) ])
                for idx in range(0, self.items_per) ])
            form.append(f.to_dnf())
        return form

    def one_in_each(self):
        """
        Gets the formula where every value in a group must belong to different root values
        :return List<Expr>: a list of subformulae that when Anded together creates the formula for this rule
        """
        form = []
        for group in range(0, len(self.groups)):
            f = And(*[
                OneHot(*[ self.X[group, idx, root]
                    for idx in range(0, self.items_per) ])
                for root in range(0, self.items_per) ])
            form.append(f.to_dnf())
        return form

    def are_same(self, value1, value2):
        """
        Returns the formula where the two given (non-root) values are a match-- they occur at the same root value
        :param value1: str- an english variable that is in self.groups
        :param value1: str- an english variable that is in self.groups, that is not in the same category as value1
        :return Expr: the formula for this clue
        """
        (group_1, val_1) = self.get_val_tuple(value1)
        (group_2, val_2) = self.get_val_tuple(value2)
        f_aresame = Or(*[ And(self.X[group_1, val_1, idx], self.X[group_2, val_2, idx])
                        for idx in range(0, self.items_per) ])

        return f_aresame

    def are_not(self, value1, value2):
        """
        Returns the formula where the two given (non-root) values are a not-- they do not occur at the same root value
        :param value1: str- an english variable that is in self.groups
        :param value1: str- an english variable that is in self.groups, that is not in the same category as value1
        :return Expr: the formula for this clue
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
        :return Expr: the formula for this clue
        """
        (group, val) = self.get_val_tuple(value)
        idx = self.root_group.index(root_val)
        return self.X[group, val, idx]

    def is_not_at(self, value, root_val):
        """
        Returns the formula where the given non root value is not at the given root value
        :param value: str- the non root value that does not match with the root value
        :param root_val: str- the root value that does not match with the given category value
        :return Expr: the formula for this clue
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
        :return Expr: the formula for this clue
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
        :return Expr: the minimized form of this puzzle
        """
        esp_form, = espresso_exprs(self.formula.to_dnf())
        return esp_form

    def solve(self):
        """
        Solve this puzzle returning a valid solution and the number of total possible solutions there are
        :return Tuple<List<str>, int>: the solution to the puzzle as a list of english variable names and
                                the number of possible solutions there are in this puzzle
        """
        solved = self.formula.satisfy_one()
        sol = [self.fid_to_var(str(var)) for var in list(solved.keys()) if solved[var] == 1]
        sol.sort(key = lambda var: var.split('_')[-1])
        count = self.formula.satisfy_count()

        return (sol, count)

    def eval_clue(self, clue):
        """
        Returns the boolean formula for the given clue based on its type and values
        Raises an exception if the clue is not of a valid type
        :param clue: dict- a clue in the format of a proper JSON Clue
        :return Expr: boolean formula for the given clue
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
            raise Exception("Invalid clue type ", clue["type"])

    def rules_dnf(self):
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

        return base[0]

    def translate_f(self, formula):
        """
        Translates a formula into english variable names
        :param formula: Expr- the formula
        """
        eng_formula = re.sub('x\[\d,\d,\d\]', lambda match: self.fid_to_var(match.group()), str(formula))
        return eng_formula

    def extra_clues_help(self, rules, acc, clues):
        """
        Helper to get extraneous clue sets
        :param rules: Expr- the base formula for the rules of the puzzle
        :param acc: List- list of already extraneous clues and checks if other clues are further removable
        :param clues: List- all the clues as Expr formulae
        """
        extra = []
        remaining = [c for id, c in enumerate(clues) if not(id in acc)]
        for id, clue in enumerate(clues):
            if (id in acc):
                break

            lo_formula = [f.to_dnf() for idx, f in enumerate(remaining) if (idx != id)]
            fx = And(*(lo_formula + [rules]))
            num_sols = fx.satisfy_count()
            if num_sols == 1:
                extra.append(acc + [id])
                extra = extra + self.extra_clues_help(rules, acc + [id], clues)

        return extra

    def extra_clues(self, rules):
        """
        Gets all the possible sets of extraneous clues that could be removed from the clueset
        and still result in a single puzzle solution
        :param rules: Expr- the base formula for the rules of the puzzle
        :return List<List<int>>: a list of sets of removable clues where the clue is represented by the
                        index at which it appears in the inputted clue list starting from 0
        """
        clue_f = [self.eval_clue(clue) for clue in self.clueset]
        return self.extra_clues_help(rules, [], clue_f)

    def get_same_mapping(self):
        """
        Gets a dictionary where each key and value pair have a SAMEAS clue associating them. Each key
        only has one such value, even if it has multiple SAMEAS relations, and it will ues the relation
        of the last clue in the clueset.
        :return Dict: the SAMEAS variable mapping from the clue set
        """
        sames = {}
        for clue in self.clueset:
            if clue["type"] == SAME:
                sames[clue["vals"][0]] = clue["vals"][1]
                sames[clue["vals"][1]] = clue["vals"][0]

        return sames

    def new_xaway_clue(self, sames, clue_vals):
        """
        Creates a new equivalent XAWAY clue by replacing the given clue values with other variables
        that are known to be at the same root based on the given sames mapping.
        If there are no alternate mappings, then returns None
        :param sames: Dict- the SAMEAS variable mapping from the clue set
        :param clue_vals: List- the vals field of a XAWAY clue
        :return Dict: A full XAWAY clue in the standard json format that is equivalent to the given values or None
        """
        val0 = sames.get(clue_vals[0])
        val1 = sames.get(clue_vals[1])

        if (not val0 and not val1):
            return None

        return {
            "type": XAWAY,
            "vals": [val0 or clue_vals[0], val1 or clue_vals[1], clue_vals[2]]
        }

    def alt_clueset(self):
        """
        Returns an alternative clueset that replaces all XAWAY clues with a logically equivalent
        clue, such that the puzzle solution is still the same single valid solution. An alternative
        clueset is only possible for puzzles that contain at least one XAWAY and one SAMEAS clue
        that share a common variable (per the transitive property).
        :return List<Clue>: List of clues in the expected json format
        """
        sames = self.get_same_mapping()
        new_clues = []
        has_changes = False

        for clue in self.clueset:
            if (clue["type"] == XAWAY):
                alt = self.new_xaway_clue(sames, clue["vals"])
                if alt:
                    new_clues.append(alt)
                    has_changes = True
            else:
                new_clues.append(clue)

        return new_clues if has_changes else None

    def run(self, op):
        """
        Run the grid puzzle evaluation based on the given process type and prints the results
        :param op: str- the type of additional operations to run on the logic puzzle
        """
        rules = self.rules_dnf()
        self.formula.append(rules)
        try:
            clue_form = [self.eval_clue(clue) for clue in self.clueset]
        except Exception as e:
            print("Invalid input: check the format of puzzle clues")
            print(e)
            return
        self.formula = self.formula + clue_form
        self.formula = And(*[f.to_dnf() for f in self.formula ])

        sol, count = self.solve()
        print("Number of possible solutions: ", count)
        print("Solution:")
        print(sol)

        if (op == "NONE"):
            return

        if (op == "MIN" or op == "ALL"):
            print("\n\nMinimized formula:")
            print(self.translate_f(self.eval_espresso()))

        if (op == "RED" or op == "ALL"):
            print("\n\nSets of clues that can be removed to still provide a single solution:")
            print(self.extra_clues(rules))

        if (op == "ALT" or op == "ALL"):
            print("\n\nAlternative equivalent clueset example:")
            pprint(self.alt_clueset())
