
predicate P(x : int)

lemma dummyLemma()
ensures forall x :: P(x)
{
  test();
}



tactic {:partial} test(){
  
  tvar p :| p in tactic.ensures;
  //tvar p := forall x :: P(x);

  tactic forall {:vars z} p
  {
	assume false;
  }
}
