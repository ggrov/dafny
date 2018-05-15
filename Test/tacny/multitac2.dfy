
datatype Dummy = A | B
datatype Dummy2 = A2 | B2

lemma lemma1(m: Dummy)
ensures true


lemma lemma2(m: Dummy)
ensures false


lemma ltest(d : Dummy, e: Dummy)
 ensures false
{
   tac(d);
   tac(e);
}

tactic tac(b: term)
{
    tvar vs := tactic.vars + tactic.input;
    tvar ls := tactic.lemmas;	
    explore(ls, vs);
}
