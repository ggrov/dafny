
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
  //dummyLemma(d);

}

tactic tac(b: term)
{

    tvar vs := tactic.vars + tactic.input;
    tvar ls := tactic.lemmas;	
    explore(ls, vs);
}
