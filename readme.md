# CNF and D&P Algorithm Implementations

It contains code in `Haskell` which implements the procedure for
obtaining a conjunctive normal form of a given propositional formula.

The following list represents a list of the functions involved in the
the code:

1. The fnc:

		clausularform :: Formula -> Formula

1. The subsumption algorithm (limited number of variables):

		sieveClauseList :: [Ic] -> [Ic]

1. Transform a set of formulas with "and" into a set of clauses:

		form2claus :: Formula -> [[Literal]]
		setform2clausImp :: [Formula] -> [[Literal]]

1. The Davis&Putnam algorithm:

		unsatisfiable:: [[Literal]] -> Bool
		satisfiable :: [[Literal]] -> (Bool, [[Literal]])

1. The deduction theorem:

		deductionTheorem :: [Formula] -> Formula -> [Formula].

1. Semantic implication:

		sImplies :: [Formula] -> Formula -> Bool
		extsImplies :: [Formula] -> Formula -> (Bool,[Literal])

1. Recognise whether a formula is a tautology or not:

		tautological :: Formula -> Bool

1. Recognise whether two formulae are equivalent or not:

		isLogEquiv :: Formula -> Formula -> Bool


Let us nuance something else:

1. `distribute`: apply `dak` as many times as necessary to arrive at
the clause form.  It uses the `alternation` function which measures
the minimum number of times it needs to be applied.

1. `associate`: apply the `aka` function to a formula in clause form
   the minimum number of times necessary for all conjunctions and
   disjunctions to be left-associative.

1. `clausularform`: apply the above functions in the appropriate order
   to transform a formula into an equivalent formula that is in
   clausular form.

1. `form2claus`: Given a formula, the `form2claus` function extracts
   its clauses. It removes tautological clauses and repeated literals
   from each of the clauses.

1. `setform2claus`: Given a set (list) of formulas, extract their
   clauses. It removes tautological clauses and repeated literals in
   each of the clauses. So, it does the same as `form2claus` in a
   vectorized form.


1. `unsatisfiable`: Given a list of clauses, returns `True` or `False`
   depending on whether the clause set is unsatisfiable or
   satisfiable. It makes use of the Davis&Putnam algorithm.

1. `satisfiable`: Given a list of clauses, returns `True` or `False`,
   depending on whether the clause set is satisfiable or not. It also
   returns a list of literals, which when interpreted as true,
   satisfies satisfies the set; in case of being unsatisfiable, it
   gives the empty list.


1. `sImplies`: Given a set of formulae, and a formula, it says if this
   last one is a logical consequence of the previous set of formulas.

1. `extsImplies`: Same as above, except that in the case that the
   implication is false, it also gives a list of literals whose
   implication is false, showing us why the implication is false.

Here are some examples of how to use the functions included in 
`CnfDpa.hs`.

By means of `ex00` we propose an example that requires repeated use of
`dak`:

	*CnfDpa> let x = ex00 6 6
    *CnfDpa> alt x
    5
    *CnfDpa> let y = distribute x
	*CnfDpa> complejidad y
    689553
    *CnfDpa> alt y
    0

In order to exemplify the performance of `associate` we will again use
an example created  with ex00; it requires iterated use  of `lasc`. We
have the following dialog:

	*CnfDpa> let x = ex00 3 3
    *CnfDpa> let y = distribute x
    *CnfDpa> let z = associate y
    *CnfDpa> [complejidad x, complejidad y, complejidad z]
    [11,177,167]
    *CnfDpa> [longitud x, longitud y, longitud z]
    [5,11,65]
	
After successive applications of `lasc`, the evolution of the measures
`kr` and `ar` can be observed in the following dialogue:

	*CnfDpa> [kr y, kr(lasc y), kr(lasc(lasc y)),
              kr(lasc(lasc(lasc y))), kr(lasc(lasc(lasc(lasc y))))]
    [8,4,2,1,0]
    *CnfDpa> [ar y, ar(lasc y), ar(lasc(lasc y)),
              ar(lasc(lasc(lasc y))), ar(lasc(lasc(lasc(lasc y))))]
    [1,0,0,0,0]

Another example is:
	
	*CnfDpa> let x = ex00 6 6
	*CnfDpa> let x = ex00 6 6
	*CnfDpa> let y = distribute x
	*CnfDpa> let z = associate y
	*CnfDpa> [lg x, lg y, lg z]
	[11,41,117653]
	*CnfDpa> [complejidad x, complejidad y, complejidad z]
	[41,689553,659207]
	*CnfDpa> [kr y, kr(lasc y), kr(lasc(lasc y)), kr(lasc(lasc(lasc y))),
          kr(lasc(lasc(lasc(lasc y)))), kr(lasc(lasc(lasc(lasc(lasc y))))),
          kr(lasc(lasc(lasc(lasc(lasc(lasc y))))))]
	[35,17,8,4,2,1,0]
	*CnfDpa> [ar y, ar(lasc y), ar(lasc(lasc y)), ar(lasc(lasc(lasc y))),
          ar(lasc(lasc(lasc(lasc y)))), ar(lasc(lasc(lasc(lasc(lasc y))))),
          ar(lasc(lasc(lasc(lasc(lasc(lasc y))))))]
          [4,2,1,0,0,0,0]

In order to illustrate the use of clausularform we can take the
Meredith’s axiom (cfr. J.D. Monk; Mathematical Logic. Springer-Verlag)
consider the code:

	meredith :: Formula
    meredith = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (N(Fa 4)))) (Fa 3)) (Fa 5))
                 (C (C (Fa 5) (Fa 1)) (C (Fa 4) (Fa 1)))

So we will have the following dialog:

	*CnfDpa> clausularform meredith
	KKKKKKKAAAAAN1 2 3 5 N4 1 AAAAAN1 2 3 N1 N4 1 AAAAN3 3 5 N4 1 AAAAN3 3 N1 N4 1 AAAA4 3 5 N4 1
	AAAA4 3 N1 N4 1 AAAN5 5 N4 1 AAAN5 N1 N4 1
	*CnfDpa> clauses (clausularform meredith)
    [[1,N4,N1,N5],[1,N4,5,N5],[1,N4,N1,3,4],[1,N4,5,3,4],[1,N4,N1,3,N3],[1,N4,5,3,N3],
    [1,N4,N1,3,2,N1],[1,N4,5,3,2,N1]]
	
Meredith’s formula defined above is a taulogy of the propositional
classical calculus, therefore on being applied to it the function
`form2claus` the empty list must be obtained, as we can see in the
following dialog:

    *CnfDpa> form2claus meredith
    []

But if the formula is slightly modified to prevent it from being a tautology as follows:

     meredithw::Formula
     meredithw = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (Fa 4))) (Fa 3)) (Fa 5))
                   (C (C (Fa 5) (Fa 1)) (C (Fa 4) (Fa 1)))

	*CnfDpa> clauses (clausularform meredithw)
    [[1,N4,N1,N5],[1,N4,5,N5],[1,N4,N1,3,N4],[1,N4,5,3,N4],[1,N4,N1,3,N3],[1,N4,5,3,N3],
    [1,N4,N1,3,2,N1],[1,N4,5,3,2,N1]]
    *CnfDpa> form2claus meredithw
    [[1,3,N4,5]]
	
Returning to the beginning, an example of use for `setform2clausImp`
is the following:

	*CnfDpa> let x = ex00 6 6
    *CnfDpa> let y = clausularform x
    *CnfDpa> let z = clauses y
    *CnfDpa> let w = setform2clausImp [x]
    *CnfDpa> length z
     117649
    *CnfDpa> length w
     17
    *CnfDpa> w
     [[6],[7],[1,8],[2,8],[2,9],[3,8],[3,9],[3,10],[4,8],[4,9],[4,10],[5,8],[4,11],
     [5,9],[5,10],[5,11],[5,12]]
	 
Any truth evaluation of the list of n+1+comb (n+1, 2)n clauses pingeonhole n
will map n+1 objects one-to-one 2 into n slots. Of course, this cannot
be done, so the clauses must be unsatisfiable:

	*CnfDpa> unsatisfiable.palomar$3
	True
	*CnfDpa> unsatisfiable.palomar$5
	True

However, if we throw away one clause of `palomar n`, the remaining
collection of clauses is satisfiable. For example:

	*CnfDpa> let x = pigeonhole 3
    *CnfDpa> let y = delete [No(L 5),No(L 8)] x
    *CnfDpa> unsatisfiable y
     False
    *CnfDpa> satisfiable y
     (True,[N2,N10,N11,1,N0,5,N4,N3,8,N7,N6,9])

Find in the following dialog a solution to the problem of the eight
chess queens problem:

	*CnfDpa> let x = queen 8
    *CnfDpa> satisfiable x
     (True,[N7,N4,N5,N6,N15,N10,N11,N12,N13,N14,N23,N31,N27,N28,N29,N30,N39,N38,N55,N53,
     N54,N63,N57,N58,N59,N60,N61,N62,3,N2,N1,N0,9,N8,22,N21,N20,N19,N18,N17,N16,
     26,N25,N24,37,N36,N35,N34,N33,N32,47,N46,N45,N44,N43,N42,N41,N40,52,N51,N50,
     N49,N48,56])

In what follows we will take four formulas:

	example1::Formula
	example1 = C (C (C (C (A (Fa 3) (A (N(Fa 4)) (C (Fa 5) (N (K (Fa 6) (Fa 7))))))
           (C (C (Fa 1) (Fa 2)) (C (Fa 1) (Fa 4))))
           (C (N(N (C (Fa 1) (A (Fa 7) (Fa 3))))) (N(K (C (Fa 3) (C (Fa 8) (Fa 2)))
           (C (N (Fa 5)) (Fa 4)))))) (N (C (Fa 1) (A (Fa 7) (Fa 3)))))
           (C (Fa 8) (K (N (Fa 6)) (Fa 2)))
		   
	example2::Formula
	example2 = C (C (Fa 8) (K (N (Fa 6)) (Fa 2)))
           (N(K (N (Fa 3)) (N (C (Fa 4) (C (Fa 5) (N (K (Fa 6) (Fa 7))))))))


	example3::Formula
	example3 = K (C (Fa 3) (A (N(Fa 8)) (Fa 2))) (C (N (Fa 5)) (Fa 4))

	example4::Formula
	example4 = A (Fa 3) (C (Fa 4) (C (Fa 5) (N (K (Fa 6) (Fa 7)))))

and we will see that the
fourth is a consequence of the first three:

	*CnfDpa> sImplies [example1, example2, example3] example4
		True
	*CnfDpa> sImplies [example1, example3] example4
		False
	*CnfDpa> extsImplies [example1, example3] example4
		(False,[N8,2,1,7,6,5,4,N3])
