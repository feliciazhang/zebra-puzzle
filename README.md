# Logic Grid Puzzle computations and experiments
### Felicia Zhang and Sarah Coffen for CS2800

# TODOs (delete this later)
MUST DO
- write the whole report lmao
- write this readme

NICE TO DO
- add greater than/less than clue type
- update vocations puzzle input to use the new type
- update alt fxn to be more general and replace new type too

## Directory structure (sarah)

## Usage
Setup: `make`

To run the program: `./logicpuzzle <op-type> < <input_file_path>`

The puzzle input is read from the command line via standard input.
If using file, the input file must be a JSON of the expected puzzle format as described below.
Sample input files can be found in the `Test/` directory.

**op-type (required) is one of**
- `NONE`: Solve the puzzle only and show possible solution count
- `MIN`: Solve + print the minimized formula for the puzzle
- `RED`: (red => redundant) Solve + print sets of clues that could be removed from the puzzle's
clueset to provide the same single solution. This prints a list of lists, where each sublist
contains indices of clues that could be removed based on the order of the clues in the given input,
and starting at 0. A result like `[[0], [0, 3]]` means that removing clue 0, or both clue 0 and 3
from the puzzle would still result in the same single solution
- `ALT`: Solve + print an alternative clueset that is logically equivilant and will result in the same
singular valid solution. If no such clueset is possible by simple replacements in this program, it
will print None.
- `ALL`: Perform all the functionality of the previously stated op types

## Puzzle data definition
The Puzzle class serves as a representation of a logic grid puzzle and has functions to perform
various logical computations on the puzzle, including minimizing the formula, determining redundant
clues, and creating equivalent alternate clues. English puzzle clues must be translated to the
formal representation of this program, and all computations and results are in the context of
this representation.

**Representation of a logic puzzle:**

`X` - a multidimensional list of variables that are [`pyeda`](https://pyeda.readthedocs.io/en/latest/)
boolean variables, representing the puzzle variables.
Each variable is in the format of 'value_root' in english, meaning that value belongs with this root value.
Variables in X are identified by 3 indices `X[x,y,z]` where (x,y) refers to a value in the list of groups (2d list),
and z is the index of the root value associated.

For example, in a puzzle with `root_group = ["1", "2"]` and `groups = [["Alice", "Bob"], ["candy", "beans"]]`,
the English variable `beans_1` indicates the variable where the person at 1 likes beans. The data expression
for this would be `X[1,0,0]`

`root_group` `List<str>` - one of the puzzle categories to serve as root, normally chosen as the one with comparable
(eg numerical) values

`groups` `List<List<str>>` - the values in the non-root puzzle categories, separated by category

`clueset` `List<Clue>` - all puzzle clues, formatted as pythonized JSON described below

## Puzzle input format and clues (sarah)
