module CnfDpa (module CnfDpa) where

import Data.List

-- TYPE DEFINITIONS

{- 
We define the "Literal" data  type, based on integers "Int". 
-}

data Literal = L Int | No Literal deriving Eq

{-
We introduce the "Literal" type in the "Show" class, so that its instances 
are shown without parentheses.
-}

instance Show Literal where
             show (L n) = show n
             show (No p) = "N" ++ show p

{-
Now the data type "Literal" is entered in the Ord class.
-}

instance Ord Literal where
         compare (No (L n)) (L m)      = case (compare n m) of 
                                              LT -> LT
                                              GT -> GT
                                              EQ -> GT
         compare (L n) (L m)           = compare n m
         compare (No (L n)) (No (L m)) = compare n m
         compare (L n) (No (L m))      = case (compare n m) of
                                              LT -> LT
                                              GT -> GT
                                              EQ -> LT

{- 
Definition of the data type "Indexed clause" (Ic)
and introduction to "Show".
-}

data Ic = Ic (Integer,[Literal]) deriving Show

{- 
Introduction of "Ic" in "Eq" and "Ord"
-}

instance Eq Ic where
         Ic (x,l) == Ic (y,s)  = x == y
         
instance Ord Ic where
         compare (Ic (x,l)) (Ic (y,s)) = compare x y

{- 
We define the "Formula" data type, which involves writing 
The formulas in Polish form. Atomic formulas are based 
in integers of type "Int".
-}

data Formula = Fa Int 
             | N Formula
             | C Formula Formula 
             | E Formula Formula 
             | K Formula Formula 
             | A Formula Formula
               deriving (Eq, Ord)

{-
We introduce the "Formula" type in the "Show" class, so that its instances 
are shown without parentheses.
-}

instance Show Formula where
              show (Fa n)  = show n
              show (C p q) = "C" ++ show p ++ " " ++ show q
              show (E p q) = "E" ++ show p ++ " " ++ show q
              show (K p q) = "K" ++ show p ++ " " ++ show q
              show (A p q) = "A" ++ show p ++ " " ++ show q
              show (N p)   = "N" ++ show p 

-- END OF TYPE DEFINITIONS

{-
The function "ece" changes a formula to an equivalent one 
written without "E" and without "C"; that is, we suppress the double arrow
and the arrow.
-}

ece :: Formula -> Formula
ece (E p q) = K (A (N (ece(p))) (ece(q))) (A (N (ece(q))) (ece(p)))
ece (C p q) = A (N (ece(p))) (ece(q))
ece (N p) = N (ece(p))
ece (K p q) = K (ece(p)) (ece(q))
ece (A p q) = A (ece(p)) (ece(q))
ece p = p

{-
The function "brng" applied to a formula constructs another equivalent that 
has the negation symbols next to the atomic formulas.
-}

brng :: Formula -> Formula
brng (N (K p q)) = A (brng (N p)) (brng (N q))
brng (N (A p q)) = K (brng (N p)) (brng (N q))
brng (K p q) = K (brng(p)) (brng(q))
brng (A p q) = A (brng(p)) (brng(q))
brng (N (N p)) = brng p
brng (N p) = N p
brng p = p


{- IN WHAT FOLLOWS, WE APPLY THE DISTRIBUTIVE PROPERTY UNTIL WE REACH 
A CLAUSULAR FORM. THIS IS ACHIEVED WITH THE FUNCTION "distribute"-}

{- Every time it finds the sequence "A-K" it applies the distributive law
of the disjunction with respect to the conjunction.  Later the
number of times it needs to be applied in the process is computed. 
This will be done with the function "alt" -}

dak :: Formula -> Formula
dak (A p q) 
    | p == q = dak p    
dak (A (K p q) r) = K (dak (A p r)) (dak (A q r))
dak (A r (K p q)) = K (dak (A r p)) (dak (A r q))
dak (A p q) = A (dak (p)) (dak (q))
dak (K p q)
    | p == q = dak p
    | otherwise = K (dak (p)) (dak (q))
dak (N p) = N p
dak (Fa n) = Fa n


{- The "belongK" function looks if there is any conjunction in the formula
(The definition pattern is deliberately incomplete because the use
so advises) -}

belongK :: Formula -> Bool
belongK (Fa n) = False
belongK (K x y) = True
belongK (A x y) = (belongK x) || (belongK y)
belongK _ = False

{- The "alt" function measures the maximum number of "Aes" above a "K" in the
incomplete pattern formula. This function will give us the minimum  number
of times that will have to apply the distributive property of
the "OR" with respect to the "AND" to obtain combinations of clauses -}

alt :: Formula -> Int
alt (K x y) = maximum[alt x, alt y]
alt (A x y) 
   | belongK x || belongK y = 1 + maximum[alt x, alt y] 
   | otherwise                    = 0
alt _ = 0

{- "distribute" applies "dak" as many times as necessary to reach the
clausular form. It uses the "alt" function, that measures the
minimum number of times it is necessary to apply it.-}

distribute:: Formula -> Formula
distribute a = (iterate dak a)!!(alt a)

{- NOW LET'S ASSOCIATE TO THE LEFT, BOTH CONJUNCTION AND DISJUNCTION.  
THIS IS ACHIEVED WITH THE FUNCTION "asociate"-}

{- "lasc" associates on the left both conjunctions and disjunctions. The
The number of times it has to be applied will be calculated later, with the
function "iterationslasc" -}

lasc :: Formula -> Formula
lasc(A p (A q r)) = A (lasc(A p q)) (lasc(r))
lasc(K p (K q r)) = K (lasc(K p q)) (lasc(r))
lasc (A p q) 
     | p == q    = lasc(p)
     | otherwise = A (lasc(p)) (lasc(q))
lasc (K p q)
     | p == q    = lasc(p)
     | otherwise = K (lasc(p)) (lasc(q))
lasc p = p

{- "kr" counts the number of times in a formula that the right conjunction becomes a conjunction again. 
It only applies to formulas that are in clausular form. So that the case does not count if the right formula 
is not a conjunction and for that reason we must introduce the last -1 value in the definition. -}

kr :: Formula -> Int
kr (K x y) = maximum[kr x, 1+kr y]
kr x = -1

{- "ar" counts in a formula in clausular form the number of times  that the right formula in a  
disjunction is a disjunction again. With the aim that it does not count the case in which the 
right formula of a disjunction is not a disjunction, we must introduce the last -1 value in the definition -}

ar :: Formula -> Int
ar (A x y) = maximum[ar x, 1+ar y]
ar (K x y) = maximum[ar x, ar y]
ar x = -1

{- "iterationslasc" count the number of times we have to apply the function "lasc" so that 
in a formula in clausular form, both conjunctions and disjunctions are associated on the left. -}

iterationslasc :: Formula -> Int
iterationslasc x 
  | y < 1    = 0 
  |otherwise = truncate((log (fromIntegral y)) / log 2) + 1
 where y = maximum[ar x,kr x]

{- "asociate" Apply the "lasc" function to a formula in clausular form the minimum number of times 
necessary so that all conjunctions and disjunctions are associated on the left. -}

asociate :: Formula -> Formula
asociate a = (iterate lasc a)!!(iterationslasc a)


{- JOINING THE PREVIOUSLY DEFINED FUNCTIONS, WE OBTAIN THE
"clausularform" FUNCTION, WHICH TRANSFORMS ONE FORMULA INTO ANOTHER
EQUIVALENT TO IT IN CLAUSULAR FORM AND WITH THE CONJUNCTIONS AND
DISJUNCTIONS ASSOCIATED BY THE LEFT -}


clausularform :: Formula -> Formula
clausularform = asociate.distribute.brng.ece

{- A version that seems not to be effective in some examples, would be
clausularform :: Formula -> Formula
clausularform = asociate.distribute.asociate.brng.ece -}


{-
FUNCTIONS TO MANAGE THE DATA TYPE Ic
-}

-- BEGINNING

{-
p is a list of primes. The most convenient would be to put here the list of enough primes,
so as never to fall short. It does not need to be a very efficient implementation because 
we will never get too high.
-}

criba :: [Integer] -> [Integer]
criba (p:xs) = [x | x <- xs, mod x p /= 0]

primes :: [Integer]
primes = map head(iterate criba [2..])

p :: [Integer]
p = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

{-
Test:
      (take 168 primes) == p 
-}

{-
The function "clauseIndexAux" associates to each clause, view
as a list of literals, a number that is the product of
Cousins. We assign to the positive literals the primes
that occupy an even position in the list and the negatives
those who occupy an odd position. The empty list is assigned the value 1 
because the function has been implemented with multiplication.
-}

clauseIndexAux :: [Literal] -> Integer
clauseIndexAux [] = 1
clauseIndexAux ((L n):x) = (p!!(2*n)) * (clauseIndexAux x) 
clauseIndexAux ((No (L n)):x) = (p!!(2*n+1)) * (clauseIndexAux x)

{-
"clauseIndexAuxE" is like "clauseIndexAux" but using the total list of primes
-}

clauseIndexAuxE :: [Literal] -> Integer
clauseIndexAuxE [] = 1
clauseIndexAuxE ((L n):x) = (primes!!(2*n)) * (clauseIndexAuxE x) 
clauseIndexAuxE ((No (L n)):x) = (primes!!(2*n+1)) * (clauseIndexAuxE x)

{-
"clauseIndex" associates to each clause "c", seen as a list of literals, the element of type "Ic" 
consisting of the clause preceded by the product of primes that produces on it "clauseIndexAux"
-}

clauseIndex :: [Literal] -> Ic
clauseIndex l = Ic (clauseIndexAux l,l)

{-
"icFst" and "icSnd" extracts components from instances of the data type "Ic"
-}

icFst :: Ic -> Integer
icFst (Ic x) = fst x

icSnd :: Ic -> [Literal]
icSnd (Ic x) = snd x

{-
"sieve" takes a list of instances of "Ic" and deletes from it entries 
that have a multiple of the number of the number occupied by the head
-}

sieve :: [Ic] -> [Ic]
sieve (x:xs) = [y | y <- xs, mod (icFst y) (icFst x) /= 0]

{-
"sieveClauseList" deletes from a list of instances of type "Ic"
those that have as its first component a multiple of the first component 
of another entry in the list.
-}

sieveClauseList :: [Ic] -> [Ic]
sieveClauseList [] = []
sieveClauseList l@(x:xs) = x:sieveClauseList(sieve l)

-- END of handling instances of data type "Ic"


{- ONCE THE CLAUSULAR FORM OF A FORMULA HAS BEEN OBTAINED, WE WILL MANAGE THE FORMULAS 
THAT RESULT FROM APPLYING "clausularform" -}

{- First, we transform a clause into a list of literals. For this, we will use the "literal" data type 
that we defined at the beginning. The function "literals", which performs this action is partially defined, 
since it is an auxiliary function that will only be applied to formulas that are clauses. 
Previously, we translated atomic formulas into literal ones.-}

{- Translation of atomic formulas and their denials to literals-}

atm2lit :: Formula -> Literal
atm2lit (Fa n) = L n
atm2lit (N (Fa n)) = No (L n)
atm2lit _ = L (-2) --error "The formula is not a literal"

literals :: Formula -> [Literal]
literals (A x y) = (atm2lit y) : (literals x)
literals x = [atm2lit x]

{- The next step is to transform a formula in clausular form into a list of clauses;
that is, list of literal lists. This is achieved with "clauses" -}

clauses :: Formula -> [[Literal]]
clauses (K x y) = (literals y):(clauses x)
clauses x = [literals x]

{- Once we have transformed a formula into clausular form (seen as a list of literal lists), 
we will eliminate the clauses that are tautological. For this, we previously order the literals
of a clause, and if a literal and its negated appear together, then the clause will be a tautology.-}

{- "sortSrAux" Removes repeated items from an ordered list. Go through that list, 
and only place an item if it's different from the next one. -}

sortSrAux:: Eq a => [a] -> [a]
sortSrAux [] = [] 
sortSrAux [x] = [x]
sortSrAux (x:xs)
  | x == h    = s
  | otherwise = x:s
          where h = head xs      
                s = sortSrAux xs

{- "sortSr" aplies "sortSrAux" to a list already sorted using "sort". 
This has been shown to be more efficient than the primitive function "nub"-}

sortSr:: Ord a => [a] -> [a]
sortSr = sortSrAux.sort

{- "isTautological" go through a list of literals, and if it find together with a literal with its complement, responds True. 
But, it only gives us the correct answer if the list has been previously sorted.-}

isTautological::[Literal] -> Bool
isTautological [x] = False
isTautological (x:xs) = head xs == No x || isTautological xs
isTautological _ = False

{- Given a list of clauses, "redClausularForm" remove clauses that are tautological.-}

redClausularForm :: [[Literal]] -> [[Literal]]
redClausularForm []   = []
redClausularForm (x:xs)
   | isTautological y = redClausularForm xs
   | otherwise        = y:(redClausularForm xs)
      where y = sortSr x                

{- Given a formula, the function "form2claus" extracts its clauses; also eliminate tautological 
clauses and repeated literals from each of the clauses. -}

form2claus :: Formula -> [[Literal]]
form2claus = sortSr.redClausularForm.clauses.clausularform

{- The next step is to transform a set of formulas into a list of literals. 
We will do this by concatenating the result of applying the "form2claus" function to each of the formulas. 
Since the order in which the clauses appear is not important, we will replace the "++" function with 
the "concatenate" function, which we will define. -}

concatenateAux :: [a] -> [a] -> [a]
concatenateAux [] l = l
concatenateAux (x:xs) l = concatenateAux xs (x:l)

concatenate :: [[a]] -> [a]
concatenate = foldr (concatenateAux) []

{-"setform2claus", Given a set (list) of formulas, it extracts its clauses.  
Eliminate the tautological clauses and repeated literals in each of the clauses.-}

setform2claus :: [Formula] -> [[Literal]]
setform2claus = concatenate.(map form2claus)

setform2clausImp :: [Formula] -> [[Literal]]
setform2clausImp = (map icSnd).sieveClauseList.sortSr.(map clauseIndex).redClausularForm.concatenate.(map clauses).(map clausularform)

{- WE WILL IMPLEMENT HERE THE DAVIS-PUTNAM ALGORITHM -}

{- Given a formula, "c" gives it a negation, unless the formula is the negation of an atomic formula, 
in which case "c" removes it.-} 

c :: Literal -> Literal
c (No (L n)) = L n
c (L n )     = No (L n)

{- Given a literal and a list of clauses, divide the list into three sublists: 
The one formed by the clauses that have the literal, the one formed by the clauses that have their complementary, and the one formed by the clauses that have neither the literal nor the complementary. The clauses in the first sublist are deleted; in the clauses of the second sublist eliminate the complementary (but leaves the original clause), and the clauses of the third sublist, are leaved as they are -}

dp :: Literal -> [[Literal]] -> [[Literal]]
dp l [] = []
dp l (x:xs) 
  | elem l x     = dp l xs
  | elem (c l) x = (delete (c l) x):(dp l xs)
  | otherwise    = x:(dp l xs)
  
{- The function "unsatisfiable" gives True or False, depending on whether a list of clauses (seen as lists of literals), is unsatisfiable or not. The base cases are when the clause list is empty, in which case it returns False, or when one of the clauses is the empty clause, in which case returns True. The recursive step is to apply the unique rule of the Davis-Putnam algorithm. Applying the single rule within the "unsatisfiable" function saves us memory usage, thanks to lazy evaluation, since sometimes it will not be necessary to calculate "unsatisfiable". -}
   
unsatisfiable:: [[Literal]] -> Bool
unsatisfiable [] = False
unsatisfiable l
   | elem [] l = True
   | otherwise =  unsatisfiable h && unsatisfiable s 
    where
      u = head(head l)
      h = dp u l
      s = dp (c u) l

{- "satisfiable" is an alternative to "unsatisfiable": if you
provides a set of clauses determines whether it is satisfyable or not
and, if so, it provides an interpretation that satisfies him.
It uses "satisfiableAux" providing the empty list as the second argument.  -}
      
satisfiableAux :: [[Literal]] -> [Literal] -> (Bool, [Literal])
satisfiableAux [] ls = (True,ls) 
satisfiableAux l ls
   | elem [] l     = (False, [])
   | fst k == True = k
   | otherwise     = satisfiableAux s ((c u):ls)
    where
      u = head(head l)
      h = dp u l
      s = dp (c u) l    
      k = satisfiableAux h (u:ls)

satisfiable :: [[Literal]] -> (Bool, [Literal])
satisfiable c = satisfiableAux c []


{- CLASSIC PROBLEMS-}

{-The function "deductionTheorem" applied to a list of formulas and a particular formula, transforms the problem of semantic implication into a problem of unsatisfiability, applying the deduction theorem if possible -}

deductionTheorem :: [Formula] -> Formula -> [Formula]
deductionTheorem xs (C x y)    = deductionTheorem (x:xs) y
deductionTheorem xs (A x y)    = deductionTheorem ((N x):xs) y
deductionTheorem xs (N(K x y)) = deductionTheorem (x:xs) (N y)
deductionTheorem xs y          = (N y):xs

{-FIRST PROBLEM: SEMANTIC IMPLICATION -}

{- Given a set (list) of formulas and a formula, the function
"sImplies" returns True if the first set implies
semantically to the formula, and False otherwise -}

sImplies :: [Formula] -> Formula -> Bool
sImplies xs x = unsatisfiable.setform2clausImp.deductionTheorem xs $ x


{- If "x" is a set of formulas and "x" is a formula, "sImpliesExt" responds (True,[]) if "xs" semantically implies "x", and responds (False, (l) if it does not involve it. In such a case, "l" is a list of literals that, interpreted as true, shows us that the implication is false.-}

extsImplies :: [Formula] -> Formula -> (Bool,[Literal])
extsImplies xs x = (not(fst y),snd y)
        where y = satisfiable.setform2clausImp.deductionTheorem xs $ x
              
{- SECOND PROBLEM: TAUTOLOGY-}
              
tautological :: Formula -> Bool
tautological x = sf2c x == []                                      
             where sf2c = redClausularForm.clauses.clausularform

{- THIRD PROBLEM: LOGICAL EQUIVALENCE -}

isLogEquiv :: Formula -> Formula -> Bool
isLogEquiv x y = sImplies [x] y && sImplies [y] x


{- The following function also checks whether two formulas are
equivalent or not. But we have done the test with "a=dis 1000" and "b=imp
1000" (see below for the definition of both functions). With "isLogEquiv a
b" took approximately 2 seconds, while "isLogEquiv2 a b" took 18 -}

isLogEquiv2 :: Formula -> Formula -> Bool
isLogEquiv2 x y = tautological (E x y)
-}

{- EXAMPLES OF FORMULAS -}

-- VARIOUS EXAMPLES OF FORMULAS FOR TESTS OF THE NORMAL CONJUNCTIVA FORM

u10 = K (Fa 10)(Fa 11)
u9 = K (Fa 9) u10
u8 = K (Fa 8) u9
u7 = K (Fa 7) u8
u6 = K (Fa 6) u7
u5 = K u6 (Fa 5)
u4 = K (Fa 4) u5
u3 = K (Fa 3) u4
u2 = K (Fa 2) u3
u1 = K (Fa 1) u2

x1=E (Fa 1) (Fa 2) :: Formula  -- x1 = p1 <-> p2
x2=K (Fa 2) (Fa 1) :: Formula  -- x2 = p2 ^ p1
x3=C (Fa 1) (Fa 2) :: Formula  -- x3 = p1 -> p2
x4=N x3 :: Formula  -- ¬(p1 -> p2)
x5=A x4 x2 :: Formula -- ¬(p1 -> p2) v (p1 <-> p2) 
x6=N x5 :: Formula  -- ¬(¬(p1 -> p2) v (p1 <-> p2))
x7=N x1 :: Formula -- ¬(p1 <-> p2)
x=A x6 x7 :: Formula -- ¬(¬(p1 -> p2) v (p1 <-> p2)) v ¬(p1 <-> p2)

y1 = ece x
y2 = y1
y3 = brng y2
y4 = dak y3
y5 = dak y4
y6 = lasc y5
y7 = lasc y6

z2 = K (Fa 1) (Fa 2)
z3 = K (Fa 3) z2
z4 = K (Fa 4) z3
z5 = K (Fa 5) z4
z6 = K (Fa 6) z5
z7 = K (Fa 7) z6
z8 = K (Fa 8) z7
z9 = K (Fa 9) z8
z10= K (Fa 10) z9
z11= K (Fa 11) z10
z12= K (Fa 12) z11
z13= K (Fa 13) z12
z14= K (Fa 14) z13
z15= K (Fa 15) z14
z16= K (Fa 16) z15
z17= K (Fa 17) z16
z18= K (Fa 18) z17


{- Create a formula consisting solely of conjunctions ... and others -}

f :: Int -> Int -> Formula
f 0 n = K (Fa n) (N (Fa n))
f m n = K (f (m-1) n) (f (m-1) (n+2^(m-1)))

g:: Int -> Int -> Formula
g 0 n = A (K (K (K (Fa (n+1)) (Fa (n+2))) (Fa (n+3))) (K (Fa (n+4)) (Fa (n+5)))) (K (Fa (n+6)) (Fa (n+7)))
g m n = A (K (K (K (g (m-1) (7^m)) (g (m-1) (7^m+7^(m-1)))) (g (m-1) (7^m+2*7^(m-1)))) (K (g (m-1) (7^m+3*7^(m-1))) (g (m-1) (7^m+4*7^(m-1))))) (K (g (m-1) (7^m+5*7^(m-1))) (g (m-1) (7^m+6*7^(m-1))))

h:: Int -> Int -> Formula
h 0 n = A (K (Fa (n+1)) (Fa (n+2))) (K (Fa (n+3)) (Fa (n+4))) 
h m n = A (K (h (m-1) (m)) (Fa 1)) (Fa 2)

{- Some examples of tautologies -}

taut1::Formula
taut2::Formula
taut3::Formula
taut31::Formula
taut32::Formula
taut33::Formula
taut4::Formula
taut41::Formula
taut42::Formula
taut43::Formula
modponen::Formula
modtol::Formula
peirce::Formula
silogismo1::Formula
silogismo2::Formula


taut1 = C (C (Fa 1) (C (Fa 2) (Fa 3))) (C (C (Fa 1) (Fa 2)) (C (Fa 1) (Fa 3))) 
        -- (p -> (q -> r))-> ((p -> q) -> (p -> r))

taut2 = C (C (C (C (Fa 1) (Fa 2)) (Fa 2)) (C (Fa 3) (Fa 2))) (C (Fa 1) (C (Fa 3) (Fa 2))) 
        -- (((p -> q) -> q) -> (r -> q)) -> (p -> (r -> q))

taut3 = C (C (C (C (C (Fa 1) (Fa 2)) (C (N (Fa 3)) (N (Fa 4)))) (Fa 3)) (Fa 5)) (C (C (Fa 5) (Fa 1)) (C (Fa 4) (Fa 1))) 

taut31 = C (C (C (C (Fa 1) (Fa 2)) (C (N (Fa 3)) (N (Fa 4)))) (Fa 3)) (Fa 5) 
         -- (((p -> q) -> (¬r -> ¬s)) -> r) -> t

taut32 = C (Fa 5) (Fa 1) -- t -> p

taut33 = C (Fa 4) (Fa 1) -- s -> p

taut41 = C (C (Fa 1) (Fa 2)) (Fa 3)

taut42 = C (Fa 2) (C (Fa 3) (Fa 5))

taut43 = C (Fa 2) (Fa 5)

taut4  = C (taut41) (C (Fa 4) (C (taut42) (taut43)))

         -- taut3 = (taut31 -> (taut32 -> taut33))

modponen = C (K (Fa 1) (C (Fa 1) (Fa 2))) (Fa 2) 
           -- (p ^ (p -> q)) -> q

modtol = C (K (C (Fa 1) (Fa 2)) (N (Fa 2))) (N (Fa 1)) 
         -- ((p -> q) ^ ¬q) -> ¬p

peirce = C (C (C (Fa 1) (Fa 2)) (Fa 1)) (Fa 1) 
         -- ((p -> q) -> p) -> p

silogismo1 = C (C (Fa 1) (Fa 2)) (C (C (Fa 2) (Fa 3)) (C (Fa 1) (Fa 3))) 
             -- (p -> q) -> ((q -> r) -> (p -> r))

silogismo2 = C (C (Fa 2) (Fa 3)) (C (C (Fa 1) (Fa 2)) (C (Fa 1) (Fa 3))) 
             -- (q -> r) -> ((p -> q) -> (p -> r))

-- SEVERAL EXAMPLES TO TEST THE DAVIS-PUTNAM ALGORITHM


tau::[[Literal]]
tau = [[No (L 1), L 2, L 3], [L 1, L 2, No (L 3)],[No (L 1), L 3],[L 2, No (L 3)]]

f2lit::Formula -> Literal
f2lit (Fa n) = L n
f2lit (N (Fa n)) = No(L n)
f2lit _ = L (-1)

lit2:: [[Formula]] -> [[Literal]]
lit2= map(map f2lit)

{- Examples of clause sets -}

gamma0::[[Literal]]
gamma0 = [[L 1, L 2],[No(L 1), L 2],[L 1, No(L 2)],[No(L 1), No(L 2)]]

gamma1::[[Literal]]
gamma1 = [[L 1, No(L 2), No(L 3)],[No(L 1), No(L 2), L 3],[L 1, L 2, No(L 3), L 4],[No(L 4)]]

gamma2::[[Literal]]
gamma2 = [[No(L 1), No(L 2), L 3],[L 1, No(L 2)],[L 2],[No(L 3)]]

gamma3::[[Literal]]
gamma3 = [[L 1, L 3],[No(L 2), L 3],[L 4],[No (L 2), No(L 3), L 5],[L 2], [No(L 5)]]

gamma4::[[Literal]]
gamma4 = [[L 1, L 3],[No(L 2), L 3],[L 4],[No (L 2), No(L 3), L 5],[L 2]]

gamma5::[[Literal]]
gamma5 = [[L 1, L 2],[No(L 1),L 2],[No(L 1),No(L 2)]]

gamma6::[[Literal]]
gamma6 = [[No (L 1), L 1, L 3],[L 2,L 3],[No(L 1),L 3,L 4,L 5],[No (L 5)],[L 1,No(L 3),No (L 4)]]

gamma7::[[Literal]]
gamma7 = [[No (L 1), L 1, L 3],[L 2,L 3],[No(L 1),L 3,L 4,L 5],[No (L 5)],[L 1,No(L 3),No (L 4)],
          [No (L 1),No (L 4)],[L 3, No (L 4)]]
         
gamma8::[[Literal]]
gamma8 = [[No (L 1), L 1, L 3],[L 2,L 3],[No(L 1),L 3,L 4,L 5],[No (L 5)],[L 1,No(L 3),No (L 4)],
          [No (L 1),No (L 4)],[L 3, No (L 4)],
          [L 1,L 4],[No (L 3),L 4]
          ]
         
meredith::Formula
meredith = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (N(Fa 4)))) (Fa 3)) (Fa 5)) (C (C (Fa 5) (Fa 1)) (C (Fa 4) (Fa 1)))

comprobacionMeredith::Formula
comprobacionMeredith = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (N(Fa 4)))) (Fa 3)) (Fa 5)) (C (C (Fa 5) (Fa 1)) (Fa 1))

mert1 :: Int -> Int -> Formula
mert1 m 1 = A (K (Fa m) (N(Fa 1))) (Fa (m+1)) 
mert1 m n = A (K (Fa m) (N(Fa 1))) (mert1 (m+1) (n-1))

meredithFa1 :: Int -> Formula
meredithFa1 n = C (C (C (C (C (mert1 (2) (n)) (Fa 2)) (C (N(Fa n)) (N(Fa 4)))) (Fa n)) (Fa 5)) (C (C (Fa 5) (mert1 (2) (n))) (C (Fa 4) (mert1 (2) (n))))

meredithFa2 :: Int -> Formula
meredithFa2 n = C (C (C (C (C (Fa 1) (mert1 (2) (n))) (C (N(Fa n)) (N(Fa 4)))) (Fa n)) (Fa 5)) (C (C (Fa 5) (Fa 1)) (C (Fa 4) (Fa 1)))

meredithFa3 :: Int -> Formula
meredithFa3 n = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(mert1 (2) (n))) (N(Fa 4)))) (mert1 (2) (n))) (Fa 5)) (C (C (Fa 5) (Fa 1)) (C (Fa 4) (Fa 1)))

meredithFa4 :: Int -> Formula
meredithFa4 n = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (N(mert1 (2) (n))))) (Fa 3)) (Fa 5)) (C (C (Fa 5) (Fa 1)) (C (mert1 (2) (n)) (Fa 1)))

meredithFa5 :: Int -> Formula
meredithFa5 n = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (N(Fa 4)))) (Fa 3)) (mert1 (2) (n))) (C (C (mert1 (2) (n)) (Fa 1)) (C (Fa 4) (Fa 1)))

meredith1::Formula              
meredith1 = C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (N(Fa 4)))) (Fa 3)) (Fa 5)

meredith2::Formula
meredith2 = C (Fa 5) (Fa 1)

meredith3::Formula
meredith3 = Fa 4

meredith4::Formula
meredith4 = Fa 1

meredithmal::Formula
meredithmal = C (C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (Fa 4))) (Fa 3)) (Fa 5)) (C (C (Fa 5) (Fa 1)) (C (Fa 4) (Fa 1)))

meredith1mal::Formula              
meredith1mal = C (C (C (C (Fa 1) (Fa 2)) (C (N(Fa 3)) (Fa 4))) (Fa 3)) (Fa 5)

meredithArt1::Formula
meredithArt1 = C (C (C (C (A (Fa 3) (A (N(Fa 4)) (C (Fa 5) (N (K (Fa 6) (Fa 7)))))) (C (C (Fa 1) (Fa 2)) (C (Fa 1) (Fa 4)))) (C (N(N (C (Fa 1) (A (Fa 7) (Fa 3))))) (N(K (C (Fa 3) (C (Fa 8) (Fa 2))) (C (N (Fa 5)) (Fa 4)))))) (N (C (Fa 1) (A (Fa 7) (Fa 3))))) (C (Fa 8) (K (N (Fa 6)) (Fa 2)))

meredithArt2::Formula
meredithArt2 = C (C (Fa 8) (K (N (Fa 6)) (Fa 2))) (N(K (N (Fa 3)) (N (C (Fa 4) (C (Fa 5) (N (K (Fa 6) (Fa 7))))))))

meredithArt3::Formula
meredithArt3 = K (C (Fa 3) (A (N(Fa 8)) (Fa 2))) (C (N (Fa 5)) (Fa 4)) 

meredithArt4::Formula
meredithArt4 = A (Fa 3) (C (Fa 4) (C (Fa 5) (N (K (Fa 6) (Fa 7)))))

{- 

Fa 1 = A (Fa 3) (C (Fa 4) (C (Fa 5) (N (K (Fa 6) (Fa 7)))))

Fa 2 = C (C (Fa 1) (Fa 2)) (C (Fa 1) (Fa 4))

Fa 3 = N (C (Fa 1) (A (Fa 7) (Fa 3)))

Fa 4 = K (C (Fa 3) (C (Fa 8) (Fa 2))) (C (N (Fa 5)) (Fa 4))

Fa 5 = C (Fa 8) (K (N (Fa 6)) (Fa 2))

-}

{- Test functions -}

listaAux :: Int -> [Literal]
listaAux 0 = [No (L 0), L 0]
listaAux n = [No (L n), L n] ++ listaAux(n-1)

dis :: Int -> Formula
dis 0 = Fa 0
dis n = A (Fa n) (dis (n-1))

imp :: Int -> Formula
imp 0 = Fa 0
imp n = C (N (Fa n)) (imp (n-1))

longitud :: Formula -> Int
longitud (E p q) = 1 + maximum[(longitud p),(longitud q)]
longitud (C p q) = 1 + maximum[(longitud p),(longitud q)]
longitud (A p q) = 1 + maximum[(longitud p),(longitud q)]
longitud (K p q) = 1 + maximum[(longitud p),(longitud q)]
longitud (N p) = 1 + (longitud p)
longitud _ = 0

complejidad :: Formula -> Int
complejidad (E p q) = 1 + (complejidad p) + (complejidad q)
complejidad (C p q) = 1 + (complejidad p) + (complejidad q)
complejidad (A p q) = 1 + (complejidad p) + (complejidad q)
complejidad (K p q) = 1 + (complejidad p) + (complejidad q)
complejidad (N p) = 1 + (complejidad p)
complejidad _ = 0

{- Pigeonhole principle -}

pares :: Int -> [(Int,Int)]
pares n = [(i,j) | j <- [1..n], i <- [0..j-1]]

mares :: Int -> [[(Int,Int)]]
mares n = [[(i,j)| j <- [0..n-1]] | i <- [0..n]] 

{-
"postivas" and "negativas" generate the clauses necesary to express the Pigeonhole principle (S. N. Burris, Logic for Mathematics and Computer Science, Prentice Hall, pag. 118: we use to move to our
type of formula that the application (i,j) |-> n*i+j is injective from {0,...,n}x{0,...,n-1} in |N).  
Once generated, the union of clauses is made  with "palomar" and to what results can be then applied "satisfiable" or "unsatisfiable". With this last function it have to give "True" for all n, which is just what the Pigeonhole principle assures.
-}

negativas :: Int -> [[Literal]]
negativas n = [[No(L(n*i+k)),No(L(n*j+k))] | j <- [1..n], i<- [0..j-1], k <- [0..n-1]]

positivas :: Int -> [[Literal]]
positivas n = [[L(i*n+j) | j <- [0..n-1]] | i <- [0..n]]

palomar :: Int -> [[Literal]]
palomar n = concatenate [positivas n, negativas n]

{- 
The execution of "unsatisfiable (palomar n)" took:

for n=1,   0'00 seg;   0'00 seg. iMac;     0'00 lenovo x220i;          516480 bytes 
for n=2,   0'00 seg;   0'00 seg. iMac;     0'00 lenovo x220i;          551992 bytes
for n=3,   0'01 seg;   0'01 seg. iMac;     0'01 lenovo x220i;         1105528 bytes
for n=4,   0'04 seg;   0'03 seg. iMac;     0'10 lenovo x220i;         3915176 bytes
for n=5,   0'25 seg;   0'33 seg. iMac;     0'96 lenovo x220i;        34575976 bytes
for n=6,   2'63 seg;   3'73 seg. iMac;    10'88 lenovo x220i;       381240944 bytes
for n=7,  31'62 seg;  45,93 seg. iMac;   131,49 lenovo x220i;      4581754088 bytes
for n=8, 412'77 seg; 594,64 seg. iMac;  1719.51 lenovo x220i;     59271449008 bytes
-}  

{- n Queens on a board of size nxn -}

{- Given a chessboard of n rows and n columns, it is
place in it n queens so that no attack on a different one -}

{- We number the rows and columns from 0 to n-1. The box that is in the i-th row and j-th column 
corresponds to the N*I+J number. In this way, each cell corresponds to a unique number between 0 and n^2-1 -}

{- We will represent by the literal L(m) the fact that the box m is
occupied by a queen -}

{- row n i It is a clause that expresses that in the i-th row must go a queen -}

row :: Int -> Int -> [Literal]
row n i = [L(n*i+j) | j <- [0..n-1]]

{- rowT n  is a list of clauses, which express that in each row there must be a queen -}

rowT :: Int -> [[Literal]]
rowT n = [row n i | i <- [0..n-1]]

{- column n i It is a clause that expresses that in the J-th column must go a queen -}

column :: Int -> Int -> [Literal]
column n j = [L(n*i+j) | i <- [0..n-1]]

{- columnT n It is a list of clauses, which express that in each column there must be a queen -}

columnT :: Int -> [[Literal]]
columnT n = [column n j | j <- [0..n-1]]

{- Given two cells in a row i (n*i+j and n*i+k, with j<k), the clause [No(L(n*i+j)), No(L(n*i+k))] states that there cannot be two queens in those two cells.
If we vary i between 0 and n-1, j between 0 and n-2 and k between j+1 and n-1, we get a list of clauses that mean that there cannot be two queens in the same row. We do this with the function noRow -}

noRow :: Int -> [[Literal]]
noRow n = [[No(L(n*i+j)), No(L(n*i+k))] | i <- [0..n-1], j <- [0..n-2], k <- [j+1..n-1]]

{- Given a column j, two cells in that column would be n*i+j and n*k+j,
with i<k.  The clause [No(L(n*i+j)), No(L(n*k+j))] states that there cannot be two queens in those boxes.
Varying j between 0 and n-1, i between 0 and n-2 and k between i+1 and n-1 we get a list of clauses that mean that there cannot be two queens in the same column.  The "noColumn" function constructs this list of clauses -}

noColumn :: Int -> [[Literal]]
noColumn n = [[No(L(n*i+j)), No(L(n*k+j))] | j <- [0..n-1], i <- [0..n-2], k <- [i+1..n-1]] 

{- Given a box c=n*i+j that is not in the last row or in the last column (i<n-1 and j<n-1), to move to the
right by the ascending diagonal, we add to the number that represents the box multiples of 9 (because each offset supposes increase by 1 the number of the row and the number of the column in which we are). The "NoDiagU" function gives us a list of clauses that represent that if a queen is in a box, there can be no no queen on the ascending diagonal on which it is located -}

noDiagU :: Int -> [[Literal]]
noDiagU n = [[No(L(n*i+j)), No(L(n*i+j+(n+1)*k))] | i <- [0..n-2], j <- [0..n-2], k <- [1..min (n-1-i) (n-1-j)]]

{- To move from a box c = n * i + j (that is not in the first row or in the last column) by the descending diagonal, we have to go subtracting multiples of 7, since each displacement means increasing by 1
the column number, and decrease the row number by 1. The "noDiagD" function gives us a list of clauses that represent that if a queen is in a square, there can be no queen on the descending diagonal in which it is located.-}

noDiagD :: Int -> [[Literal]]
noDiagD n = [[No(L(n*i+j)), No(L(n*i+j-(n-1)*k))] | i <- [1..n-1], j <- [0..n-2], k <- [1..min i (n-1-j)]]

{- With the "queen" function we meet all the conditions of the problem of the n queens -}

queen :: Int -> [[Literal]]
queen n = concatenate [rowT n, columnT n, noRow n, noColumn n, noDiagU n, noDiagD n]

------------------------------------------

cadena :: Int -> [[Literal]]
cadena n = [[L 1]] ++ [[No(L (i-1)),L i] | i<- [2..n]] ++ [[No(L i) | i<-[1..n]]] 

potencia :: Int -> Formula -> Formula -> Formula
potencia 0 a b = b
potencia n a b = C a (potencia (n-1) a b)

lineal :: Int -> Formula
lineal n = C (potencia n (C (Fa 1) (Fa 2)) (Fa 3)) (C (potencia n (C (Fa 2) (Fa 1)) (Fa 3)) (Fa 3))

{-
Example to check the semantic implication:

                      ¿alfa1, alfa2, alfa3 |= beta?

-}

alfa1 :: Formula 
alfa1 = C (A (Fa 1) (N (Fa 2))) (K (Fa 2) (N (Fa 3)))

alfa2 :: Formula
alfa2 = C (E (Fa 1) (Fa 2)) (Fa 3)

alfa3 :: Formula
alfa3 = K (A (Fa 1) (Fa 3)) (C (N (Fa 1)) (A (Fa 2) (Fa 3)))

beta1 :: Formula
beta1 = C (Fa 2) (A (Fa 1) (N (Fa 3)))

beta2 :: Formula
beta2 = K (A (Fa 1) (Fa 2)) (C (N (Fa 1)) (K (Fa 2) (Fa 3)))

beta3 :: Formula
beta3 = E (Fa 1) (Fa 3)

beta4 :: Formula
beta4 = C (N (Fa 1)) (C (Fa 2) (N (Fa 3)))


-- LATEST EXAMPLES --

{- Distributivity example -}

ex00A :: Int -> Int -> Formula
ex00A n 0 = Fa n
ex00A n m = K (Fa (m+n)) (ex00A n (m-1))

ex00:: Int -> Int -> Formula
ex00 1 m = ex00A 1 m
ex00 n m = A (ex00A n m) (ex00 (n-1) m)

frege :: Formula
frege = C (C (Fa 1) (C (Fa 2) (Fa 3))) (C (C (Fa 1) (Fa 2)) (C (Fa 1) (Fa 3)))

{-
Example to check the semantic implication:

                      ¿alfa1, alfa2, alfa3 |= beta?
-}

alfa1 :: Formula 
alfa1 = C (A (Fa 1) (N (Fa 2))) (K (Fa 2) (N (Fa 3)))

alfa2 :: Formula
alfa2 = C (E (Fa 1) (Fa 2)) (Fa 3)

alfa3 :: Formula
alfa3 = K (A (Fa 1) (Fa 3)) (C (N (Fa 1)) (A (Fa 2) (Fa 3)))

beta1 :: Formula
beta1 = C (Fa 2) (A (Fa 1) (N (Fa 3)))

beta2 :: Formula
beta2 = K (A (Fa 1) (Fa 2)) (C (N (Fa 1)) (K (Fa 2) (Fa 3)))

beta3 :: Formula
beta3 = E (Fa 1) (Fa 3)

beta4 :: Formula
beta4 = C (N (Fa 1)) (C (Fa 2) (N (Fa 3)))
