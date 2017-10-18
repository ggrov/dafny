function abs(x: int, y:int): bool
{
    x > 10 && y < 20
}


method m(x : int)
requires x > 10
ensures abs(x,9)
{
tac1();
}

method m1(x : int)
requires x > 10
ensures abs(x,9)
{
tac2();
}

tactic tac1()
{
tactic var p :| p in tactic.ensures;
assert p.unfold?;
}

tactic tac2()
{
tactic var p :| p in tactic.ensures;
assert p.unfold;
}

