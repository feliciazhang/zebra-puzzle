# Hi sarah read this pls

### puzzle.py
this is back when i thought we were going places. this is the thing where i had the 27 vars
like `Ruby_1` `ball_1` etc and I thought i could just minimize that, and all the clues are in
there too except i didnt implement the comparison one yet, just is and is not. was thinking we
could have this whole setup where we read in json files of info like we did in soft dev and have
the clues in certain expected json formats (again a la soft dev) and each file represents a
puzzle and we could show off a bunch during the presentation. the clues run
and minimize fine just on their own (but in a totally uninteresting way, i'm pretty sure it's
almost exactly the same as the og formula), you can just `python3 puzzle.py` it to see.

THE BEAR THAT RUINED US: `one_in_each`. this is the thing that says only one item in each category
can belong to the same "root" value. ie only one of ruby, spot, starbuck can have 1 kitten. this
as you can imagine is a giant 27 variable really long formula. but i was like this is computer,
can do big number right. it cannot. if you try to espresso on the formula that comes out of that,
it does not go. not even the espresso bit, you have to get it into dnf form to use espresso and its
the to_dnf bit that hangs. so tbh I think it's over for us on this route because this is like
a major factor in the minimization and there are no other libraries for espresso and qm is
way too difficult to translate good inputs for bc theyre all truth table based and this truth
table has 2^27 rows.

### test_logic.py
I even wrote unit tests for the above, thats how hard i thought this would work


### anotherpuzzle.py
after i gave up i tried to do it in a different rep with the 1:1:1:1 multi dimensional array that
we said we weren't gonna do bc minimizing it is just itself and also we'd have to hard code to
certain size and i got stuck basically immediately bc i just dont think you can do
array access like that like say that the ith dimension is j. anyway this is almost an exact
copy of the last file and tbh don't even bother looking at it.


### sat_utils.py and test.py
code that i straight copied off the internet (see source at top of file). it solves logic puzzle
thats about it. I haven't used any of it but is a good example for messing around with and i took
my approach from this.


# New direction?
the new direction i think we could try is about like smaller (minimal?) cluesets or something,
something about the clues in the clueset vs number of possible solutions which we had kind of
mentioned when we were talkingto jason before so it seems not bad. I was messing with `test.py`
by commenting out different clues and there is actually one useless clue in that example that
removing it will still have only 1 solution so it isnt like we thought. I just don't really know
what exactly we would be looking to find/accomplish, like there needs to be some goal still
and i think thats the main thing we need to figure out bc we cant just be like if u take some
stuff away the number changes. if we go that route the stuff we already have in `puzzle.py` will
work. tried solve_one solve_all there and it does work, even with the one_in_each. we'd just have
to flesh out more helpers for handling different clues and translating to comprehensible output.
