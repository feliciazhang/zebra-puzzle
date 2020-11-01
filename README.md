# Hi sarah read this pls
`python3 puzzle.py < Test/cats.json`

run that^^ to see how we are screwed again

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

Update: got espresso to work on the whole thing but re the screenshot i sent you the minimized version
is basically useless information. so i think we should still do something else if jason says ok.
we should check.

Update update: oneineach and onlyoneroot are fine on their own dnfed, but I cannot dnf them together.
the bear pt 2

### test_logic.py
I even wrote unit tests for the above, thats how hard i thought this would work


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

Update: minimal clue set is proven np hard so we need to do not that. the paper i read
said give up you cant do it

observation: replacing a clue with the same type of clue (or even with a "same as" clue for that var),
even w one of the same vars does not necessarily lead to the same number of possible solutions.
so the clues are very tightly linked/dependent. the only thing that does guarantee same results is
if you replace the var with something that it has a "same as" clue for, ie if you have:
```
1. Ruby has 1 more kitten than Spot

2. Spot likes to sleep
```
you can replace 1 with `Ruby has 1 more kitten than the cat that sleeps` to get the same results but
not much else will have that happen. which makes sense bc like transitive property so idk if this
is an important thing we can use.
