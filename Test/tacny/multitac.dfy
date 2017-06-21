
datatype Dummy = A | B
datatype Dummy2 = A2 | B2

lemma dummyLemma(m: Dummy)
ensures false
{
	assume false;
}

lemma ltest(d : Dummy)
 ensures false
{
  tac(d);
}

lemma ltest2(d : Dummy)
 ensures false
{

tac(d);
}

tactic tac(b: term)
{
	assert true;
	dummyTac(b);
}

tactic dummyTac (c: term)
{
	assume false;
}
