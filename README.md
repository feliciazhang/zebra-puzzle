# Logic Grid Puzzle computations and experiments
### Felicia Zhang and Sarah Coffen for CS2800

## Directory Structure
### _/**zebra-puzzle**_
`Makefile` : Setup for running the _`logicpuzzle`_ code.

`puzzle.py` : Puzzle class and functions for using [PyEDA](https://pyeda.readthedocs.io/en/latest/index.html), solving logic puzzles, and clue manipulation.

`logicpuzzle` : Executable for running the logic puzzle experiments.

`test_puzzle.py` : Tests functionality of the Puzzle class.

`README.md` : Instructions and information (_this file_).


### _/zebra-puzzle/**Test**_
`abxy.json` : 2x2 puzzle input file mentioned in the report

`cats.json` : 3x4 puzzle input file for the ["Cats in Spring"  puzzle from _aha!Puzzles_](https://www.ahapuzzles.com/logic/logic-puzzles/cats-in-spring/)

`cyclists.json` : 3x4 puzzle input file for the ["The Bike Race"  puzzle from _aha!Puzzles_](https://www.ahapuzzles.com/logic/logic-puzzles/the-bike-race/)

`vocations.json` : 3x4 puzzle input file for the ["Chosen Vocation"  puzzle from _aha!Puzzles_](https://www.ahapuzzles.com/logic/logic-puzzles/chosen-vocation/)


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

`X` - a multidimensional list of variables that are [`PyEDA`](https://pyeda.readthedocs.io/en/latest/)
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

## Puzzle input format and clues

### **Input Puzzle Format**
The input for the program is in json format with the following fields.

| Field       	| Datatype               	| Value                                                	|
|-------------	|------------------------	|------------------------------------------------------	|
| _description_ 	| string                 	| description of the puzzle, category names, clues                     	|
| _root_        	| list of string         	| values in the "root" category                        	|
| _groups_      	| list of list of string 	| Other puzzles values listed by category              	|
| _clues_       	| dictionary             	| dictionary containing "type" and "vals"              	|
<br>

#### **_Clues_ Subsection**
| Field       	| Datatype               	| Value                                                	|
|-------------	|------------------------	|------------------------------------------------------	|
| _type_        	| string                 	| clue identifier string                               	|
| _vals_        	| list of string         	| values in the clue, ordered if clue type requires it 	|

Example of JSON input:
```
{
    "description": "Example\n\nCategories: *RootCategory, FirstCategory,SecondCategory\n\nClues:\n1.first_clue\n2.second_clue\n",
    "root": ["1", "2", "3"],
    "groups": [["first", "second", "third"], ["A", "B", "C"]],
    "clues": [
        {
            "type": "ISAT",
            "vals": ["A", "1"]
        },
        {
            "type": "SAME",
            "vals": ["first", "B"]
        }
    ]
}
```
### **Clue Types**
