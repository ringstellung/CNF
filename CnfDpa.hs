module CnfDpa (module CnfDpa) where

import Data.List

-- DEFINICIONES DE TIPOS

{- 
Definimos el tipo de dato Literal; está basado en números enteros Int. 
-}

data Literal = L Int | No Literal deriving Eq

{-
Introducimos el tipo Literal en la clase Show, para que sus instancias 
sean mostradas sin paréntesis.
-}

instance Show Literal where
             show (L n) = show n
             show (No p) = "N" ++ show p

{-
Ahora es introducido en la clase Ord el tipo de datos "Literal" 
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
Definición del tipo de dato "Cláusula indexada" 
e introducción en Show.
-}

data Ic = Ic (Integer,[Literal]) deriving Show

{- 
Introducción de Ic en Eq y Ord
-}

instance Eq Ic where
         Ic (x,l) == Ic (y,s)  = x == y
         
instance Ord Ic where
         compare (Ic (x,l)) (Ic (y,s)) = compare x y

{- 
Definimos el tipo de dato Formula, que supone la escritura de 
las formulas en forma polaca. Las fórmulas atóminas están basadas 
en números enteros Int. 
-}

data Formula = Fa Int 
             | N Formula
             | C Formula Formula 
             | E Formula Formula 
             | K Formula Formula 
             | A Formula Formula
               deriving (Eq, Ord)

{-
Introducimos el tipo Formula en la clase Show, para que sus instancias 
sean mostradas sin paréntesis.
-}

instance Show Formula where
              show (Fa n)  = show n
              show (C p q) = "C" ++ show p ++ " " ++ show q
              show (E p q) = "E" ++ show p ++ " " ++ show q
              show (K p q) = "K" ++ show p ++ " " ++ show q
              show (A p q) = "A" ++ show p ++ " " ++ show q
              show (N p)   = "N" ++ show p 

-- FIN DE LA DEFINICIÓN DE TIPOS

{-
La función "ece" cambia una fórmula por otra equivalente que 
escrita sin "E" y sin "C"; es decir, suprimimos la doble flecha
y la flecha.
-}

ece :: Formula -> Formula
ece (E p q) = K (A (N (ece(p))) (ece(q))) (A (N (ece(q))) (ece(p)))
ece (C p q) = A (N (ece(p))) (ece(q))
ece (N p) = N (ece(p))
ece (K p q) = K (ece(p)) (ece(q))
ece (A p q) = A (ece(p)) (ece(q))
ece p = p

{-
La función "brng" aplicada a una fórmula construye otra equivalente que 
tiene los símbolos de negación junto a las fórmulas atómicas.
-}

brng :: Formula -> Formula
brng (N (K p q)) = A (brng (N p)) (brng (N q))
brng (N (A p q)) = K (brng (N p)) (brng (N q))
brng (K p q) = K (brng(p)) (brng(q))
brng (A p q) = A (brng(p)) (brng(q))
brng (N (N p)) = brng p
brng (N p) = N p
brng p = p


{- EN LO QUE SIGUE, APLICAMOS LA PROPIEDAD DISTRIBUTIVA HASTA LLEGAR A 
UNA FORMA CLAUSULAR. ESTO SE CONSIGUE CON LA FUNCIÓN "distribute"-}

{- Cada vez que encuentra la secuencia A-K aplica la ley distributiva
de la disyunción respecto a la conjunción.  Más adelante se medirá el
número de veces que hay que aplicarla en el proceso; esto se hará con
la función alt -}

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


{- La funcion "belongK" mira si hay alguna conjunción en la fórmula
(el patrón de definición es deliberadamente incompleto porque el uso
así lo aconseja) -}

belongK :: Formula -> Bool
belongK (Fa n) = False
belongK (K x y) = True
belongK (A x y) = (belongK x) || (belongK y)
belongK _ = False

{- La función "alt" mide el número máximo de "Aes" que hay por encima de una "K" en la
fórmula. Patrón incompleto. Esta función nos va a dar el número mínimo
necesario de veces que habrá que aplicar la propiedad distributiva de
la "o" respecto de la "y" para obtener conjunciones de cláusulas -}

alt :: Formula -> Int
alt (K x y) = maximum[alt x, alt y]
alt (A x y) 
   | belongK x || belongK y = 1 + maximum[alt x, alt y] 
   | otherwise                    = 0
alt _ = 0

{- "distribute" aplica "dak" las veces necesarias para llegar a la
forma clausular. Usa la función "alt" que nos mide el número
mínimo de veces que es necesario aplicarla.-}

distribute:: Formula -> Formula
distribute a = (iterate dak a)!!(alt a)

{- AHORA VAMOS A ASOCIAR A LA IZQUIERDA, TANTO LA CONJUNCIÓN COMO LA DISYUNCIÓN.  
ESTO SE CONSIGUE CON LA FUCIÓN "asociate"-}

{- "lasc" asocia por la izquierda la conjunción y la disyunción. El
número de veces que hay que aplicarla se calculará más adelante con la
función "iterationslasc" -}

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

{- "kr" cuenta el número de veces en que en una fórmula el conjunto
derecho de una conjunción vuelve a ser una conjunción. Sólo vale para
fórmulas que están en forma clausular. Para que no cuente el caso en
que el conjunto derecho no sea una conjunción hemos de introducir la
última igualdad de la definición. -}

kr :: Formula -> Int
kr (K x y) = maximum[kr x, 1+kr y]
kr x = -1

{- "ar" cuenta el número de veces en que en una fórmula el conjunto
disyunto derecho de una disyunción vuelve a ser una disyunción . Sólo
vale para fórmulas que están en forma clausular. Para que no cuente el
caso en que el disyunto derecho no sea una disyunción hemos de
introducir la última igualdad de la definición. -}

ar :: Formula -> Int
ar (A x y) = maximum[ar x, 1+ar y]
ar (K x y) = maximum[ar x, ar y]
ar x = -1

{- "iterationslasc" cuenta el número de veces que hemos de aplicar la
función "lasc" para que en una fórumla en forma clausular, tanto las
conjunciones como las disyunciones estén asociadas por la izquierda. -}

iterationslasc :: Formula -> Int
iterationslasc x 
  | y < 1    = 0 
  |otherwise = truncate((log (fromIntegral y)) / log 2) + 1
 where y = maximum[ar x,kr x]

{- "asociate" aplica la función "lasc" a una fórmula en forma
clausular el mínimo número de veces necesario para que todas las
conjunciones y disyunciones estén asociadas por la izquierda. -}

asociate :: Formula -> Formula
asociate a = (iterate lasc a)!!(iterationslasc a)


{- UNIENDO LAS FUNCIONES DEFINIDAS PREVIAMENTE, OBTENEMOS LA
FUNCIÓN "clausularform", QUE TRANSFORMA UNA FÓRMULA EN OTRA
EQUIVALENTE A ELLA EN FORMA CLAUSULAR Y CON LAS CONJUNCIONES Y
DISYUNCIONES ASOCIADAS POR LA IZQUIERDA -}


clausularform :: Formula -> Formula
clausularform = asociate.distribute.brng.ece

{- Una versión que parece no ser eficaz en algunos ejemplos, sería
clausularform :: Formula -> Formula
clausularform = asociate.distribute.asociate.brng.ece -}


{-
FUNCIONES PARA MANEJAR EL TIPO DE DATO Ic
-}

-- INICIO

{-
p es una lista de primos. Lo suyo sería poner aquí la 
lista de todos los primos para no quedarse nunca corto.
No hace falta que sea la implementación eficiente pues
nunca llegaremos demasiado arriba.
-}

criba :: [Integer] -> [Integer]
criba (p:xs) = [x | x <- xs, mod x p /= 0]

primes :: [Integer]
primes = map head(iterate criba [2..])

p :: [Integer]
p = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

{-
Prueba:
      (take 168 primes) == p 
-}

{-
La función clauseIndexAux asocia a cada cláusula, vista
como lista de literales, un número que es producto de
primos. Asignamos a los literales positivos los primos
que ocupan posición par en la lista y a los negativos
los que ocupan posición impar. La lista vacía lleva
asignada el valor 1, pues se ha implementado la función
con la multiplicación.
-}

clauseIndexAux :: [Literal] -> Integer
clauseIndexAux [] = 1
clauseIndexAux ((L n):x) = (p!!(2*n)) * (clauseIndexAux x) 
clauseIndexAux ((No (L n)):x) = (p!!(2*n+1)) * (clauseIndexAux x)

{-
clauseIndexAuxE es como clauseIndexAux pero usando 
la lista de primos total
-}

clauseIndexAuxE :: [Literal] -> Integer
clauseIndexAuxE [] = 1
clauseIndexAuxE ((L n):x) = (primes!!(2*n)) * (clauseIndexAuxE x) 
clauseIndexAuxE ((No (L n)):x) = (primes!!(2*n+1)) * (clauseIndexAuxE x)

{-
clauseIndex asocia a cada cláusula c, vista como lista de literales,
el elemento de tipo Ic que consiste en la cláusula precedida del número
producto de primos que produce sobre ella clauseIndexAux
-}

clauseIndex :: [Literal] -> Ic
clauseIndex l = Ic (clauseIndexAux l,l)

{-
icFst e icSnd extrae componentes de instancias del tipo de dato Ic
-}

icFst :: Ic -> Integer
icFst (Ic x) = fst x

icSnd :: Ic -> [Literal]
icSnd (Ic x) = snd x

{-
"sieve" toma una lista de instancias de Ic y suprime de ella
las entradas que tiene número múltiplo del número de la que
ocupa la cabeza
-}

sieve :: [Ic] -> [Ic]
sieve (x:xs) = [y | y <- xs, mod (icFst y) (icFst x) /= 0]

{-
"sieveClauseList" suprime de una lista de instancias del tipo Ic
aquellas que tiene por primera componente un múltiplo de la primera
componente de otra entrada de la lista.
-}

sieveClauseList :: [Ic] -> [Ic]
sieveClauseList [] = []
sieveClauseList l@(x:xs) = x:sieveClauseList(sieve l)

-- FIN manejo de instancias del tipo de dato Ic


{- UNA VEZ OBTENIDA LA FORMA CLAUSULAR DE UNA FÓRMULA, GESTIONAREMOS LAS
FÓRMULAS QUE RESULTAN DE APLICAR "clausularform" -}

{- En primer lugar, transformamos una cláusula en lista de literales. Para esto, usaremos el 
tipo de dato "literal" que hemos definido al principio. La función "literals", que realiza 
esta acción está parcialmente definida, pues es una función auxiliar que sólo se aplicará
a fórmulas que sean cláusulas. Previamente, traducimos fórmulas atómicas a literales.-}

{- Traduccion de formulas atomicas y sus negados a literales -}

atm2lit :: Formula -> Literal
atm2lit (Fa n) = L n
atm2lit (N (Fa n)) = No (L n)
atm2lit _ = L (-2) --error "la formula no es un literal"

literals :: Formula -> [Literal]
literals (A x y) = (atm2lit y) : (literals x)
literals x = [atm2lit x]

{- Lo siguiente es transformar una fórmula en forma clausular en una
lista de cláusulas (es decir, lista de listas de literales). Esto se
consigue con "clauses" -}

clauses :: Formula -> [[Literal]]
clauses (K x y) = (literals y):(clauses x)
clauses x = [literals x]

{- Una vez que hemos transformado una fórmula en forma clausular (vista
esta como lista de lista de literales), vamos a eliminar las cláusulas
que sean tautológicas. Para esto, previamente ordenamos los literales
de una cláusula, y si aparecen juntos un literal y su negado, entonces
la cláusula será una tautología.-}

{- "sortSrAux" elimina repetidos de una lista ordenada. Recorre una
lista, y sólo pone un elemento si es distinto del siguiente. -}

sortSrAux:: Eq a => [a] -> [a]
sortSrAux [] = [] 
sortSrAux [x] = [x]
sortSrAux (x:xs)
  | x == h    = s
  | otherwise = x:s
          where h = head xs      
                s = sortSrAux xs

{- "sortSr" aplica "sortSrAux" a una lista ya ordenada mediante
"sort". Esto se ha mostrado más eficiente que la función primitiva
"nub"-}

sortSr:: Ord a => [a] -> [a]
sortSr = sortSrAux.sort

{- "isTautological" recorre una lista de literales, y si encuentra
juntos a un literal y a su complemento, nos responde True. Sólo nos da
la respuesta correcta si previamente se ha ordenado la lista.-}

isTautological::[Literal] -> Bool
isTautological [x] = False
isTautological (x:xs) = head xs == No x || isTautological xs
isTautological _ = False

{- Dada una lista de cláusulas, "redClausularForm" elimina las cláusulas
 que sean tautológicas.-}

redClausularForm :: [[Literal]] -> [[Literal]]
redClausularForm []   = []
redClausularForm (x:xs)
   | isTautological y = redClausularForm xs
   | otherwise        = y:(redClausularForm xs)
      where y = sortSr x                

{-Dada una formula, la función "form2claus" extrae sus
cláusulas. Elimina las cláusulas tautológicas y los literales
repetidos de cada una de las cláusulas. Hemos añadido sortSr el día 7
de marzo de 2013-}

form2claus :: Formula -> [[Literal]]
form2claus = sortSr.redClausularForm.clauses.clausularform

{- Lo siguiente es transformar un conjunto de fórmulas en una lista de
lista de literales. Esto lo haremos concatenado el resultado de
aplicar la función "form2claus" a cada una de las fórmulas. Puesto que
el orden en que aparezcan las cláusulas no es importante,
sustituiremos la función "++" por la función "concatenate", que
definiremos.-}

concatenateAux :: [a] -> [a] -> [a]
concatenateAux [] l = l
concatenateAux (x:xs) l = concatenateAux xs (x:l)

concatenate :: [[a]] -> [a]
concatenate = foldr (concatenateAux) []

{-"setform2claus", dado un conjunto (lista) de fórmulas, extrae sus
cláuslas.  Elimina las cláusulas tautológicas y los literales
repetidos en cada una de las cláusulas.-}

setform2claus :: [Formula] -> [[Literal]]
setform2claus = concatenate.(map form2claus)

setform2clausImp :: [Formula] -> [[Literal]]
setform2clausImp = (map icSnd).sieveClauseList.sortSr.(map clauseIndex).redClausularForm.concatenate.(map clauses).(map clausularform)

{- IMPLEMENTAREMOS EL ALGORITMO DE DAVIS-PUTNAM -}

{- dado una fórmula, c le pone una negación salvo que la fórmula sea
el negado de una fórmula atómica, en cuyo caso la quita.-} 

c :: Literal -> Literal
c (No (L n)) = L n
c (L n )     = No (L n)

{- Dado un literal y una lista de cláusulas, divide la lista en tres
sublistas: La formada por las cláusulas que tienen al literal, la
formada por las cláusulas que tienen al complementario deL literal, y
la formada por las cláusulas que no tienen ni al literal ni al
complementario. Las cláusulas de la primera sublista, las elimina; en
las cláusulas de la segunda elimina el complementario (pero deja la
cláusula), y las cláusulas de la tercera, las deja igual -}

dp :: Literal -> [[Literal]] -> [[Literal]]
dp l [] = []
dp l (x:xs) 
  | elem l x     = dp l xs
  | elem (c l) x = (delete (c l) x):(dp l xs)
  | otherwise    = x:(dp l xs)
  
{- La función "unsatisfiable" devuelve True o False, dependiendo de que una lista de cláusulas 
(vistas estas como listas de literales), sea insatisfacible o no. Los casos base son cuando 
la lista de cláusulas es vacía, en cuyo caso devuelve False, o cuando una de las cláusulas
sea la cláusula vacía, en cuyo caso devuelve True. El paso recursivo consiste en aplicar 
la regla única del algoritmo de Davis-Putnam. El aplicar la regla única dentro de la 
fución "unsatisfiable" nos ahorra uso de memoria, gracias a la evaluación perezosa, ya que
en ocasiones no será necesario calcular "unsatisfiable s". -}
   
unsatisfiable:: [[Literal]] -> Bool
unsatisfiable [] = False
unsatisfiable l
   | elem [] l = True
   | otherwise =  unsatisfiable h && unsatisfiable s 
    where
      u = head(head l)
      h = dp u l
      s = dp (c u) l

{- "satisfiable" es una alternativa a "unsatisfiable": si se le
proporciona un conjunto de cláusulas determina si es satisfacible o no
y, caso de serlo, proporciona una interpretación que lo satisface.
Usa a "satisfiableAux" proporcionandole como segundo argumento la
lista vacía.  -}
      
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


{- PROBLEMAS CLÁSICOS-}

{-La función "deductionTheorem" aplicada a una lista de fórmulas, y
una fórmula transforma el problema de implicación semántica en un
problema de insatisfacibilidad, aplicando el teorema de la deducción
si fuera o fuese posible-}

deductionTheorem :: [Formula] -> Formula -> [Formula]
deductionTheorem xs (C x y)    = deductionTheorem (x:xs) y
deductionTheorem xs (A x y)    = deductionTheorem ((N x):xs) y
deductionTheorem xs (N(K x y)) = deductionTheorem (x:xs) (N y)
deductionTheorem xs y          = (N y):xs

{-PRIMER PROBLEMA: LA IMPLICACIÓN SEMÁNTICA-}

{-Dado un conjunto (lista) de fórmulas y una fórmula, la función
sImplies nos devuelve True si el primer conjunto implica
semánticamente a la fórmula, y False en caso contrario-}

sImplies :: [Formula] -> Formula -> Bool
sImplies xs x = unsatisfiable.setform2clausImp.deductionTheorem xs $ x


{-Si xs es un conjunto de fórmulas y x es una fórmula, "sImpliesExt"
responde (True,[]) si xs implica semánticamente x, y responde (False,
l) si no lo implica. En tal caso, l es una lista de literales que
interpretados como verdaderos nos muestra que la implicación es falsa-}

extsImplies :: [Formula] -> Formula -> (Bool,[Literal])
extsImplies xs x = (not(fst y),snd y)
        where y = satisfiable.setform2clausImp.deductionTheorem xs $ x
              
{-SEGUNDO PROBLEMA: TAUTOLOGÍA-}
              
tautological :: Formula -> Bool
tautological x = sf2c x == []                                      
             where sf2c = redClausularForm.clauses.clausularform

{-TERCER PROBLEMA: EQUIVALENCIA LÓGICA-}

isLogEquiv :: Formula -> Formula -> Bool
isLogEquiv x y = sImplies [x] y && sImplies [y] x


{- La siguiente función también comprueba si dos fórmulas son
equivalentes o no. Pero hemos hecho la prueba con a=dis 1000 y b=imp
1000 (ver más abajo la definción de ambas funciones). Con isLogEquiv a
b ha tardado aproximadamente 2 segundos, mientras que isLogEquiv2 a b
ha tardado 18

isLogEquiv2 :: Formula -> Formula -> Bool
isLogEquiv2 x y = tautological (E x y)
-}

{-EJEMPLOS DE FÓRMULAS-}

-- DIVERSOS EJEMPLOS DE FÓRMULAS PARA PRUEBAS DE LA FORMA NORMAL CONJUNTIVA

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


{- Crea una fórmula formada únicamente por conjunciones ... y otras -}

f :: Int -> Int -> Formula
f 0 n = K (Fa n) (N (Fa n))
f m n = K (f (m-1) n) (f (m-1) (n+2^(m-1)))

g:: Int -> Int -> Formula
g 0 n = A (K (K (K (Fa (n+1)) (Fa (n+2))) (Fa (n+3))) (K (Fa (n+4)) (Fa (n+5)))) (K (Fa (n+6)) (Fa (n+7)))
g m n = A (K (K (K (g (m-1) (7^m)) (g (m-1) (7^m+7^(m-1)))) (g (m-1) (7^m+2*7^(m-1)))) (K (g (m-1) (7^m+3*7^(m-1))) (g (m-1) (7^m+4*7^(m-1))))) (K (g (m-1) (7^m+5*7^(m-1))) (g (m-1) (7^m+6*7^(m-1))))

h:: Int -> Int -> Formula
h 0 n = A (K (Fa (n+1)) (Fa (n+2))) (K (Fa (n+3)) (Fa (n+4))) 
h m n = A (K (h (m-1) (m)) (Fa 1)) (Fa 2)

{- Algunos ejemplos de tautologías -}

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

-- DIVERSOS EJEMPLOS PARA PROBAR EL ALGORITMO DE DAVIS-PUTNAM


tau::[[Literal]]
tau = [[No (L 1), L 2, L 3], [L 1, L 2, No (L 3)],[No (L 1), L 3],[L 2, No (L 3)]]

f2lit::Formula -> Literal
f2lit (Fa n) = L n
f2lit (N (Fa n)) = No(L n)
f2lit _ = L (-1)

lit2:: [[Formula]] -> [[Literal]]
lit2= map(map f2lit)

{-Ejemplos de conjuntos de cláusulas-}

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

{-Funciones de prueba-}

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

{- Principio del Palomar -}

pares :: Int -> [(Int,Int)]
pares n = [(i,j) | j <- [1..n], i <- [0..j-1]]

mares :: Int -> [[(Int,Int)]]
mares n = [[(i,j)| j <- [0..n-1]] | i <- [0..n]] 

{-
"postivas" y "negativas" genera las cláusulas necesarias para expresar
el Principio del Palomar (S. N. Burris, Logic for Mathematics and
Computer Science, Prentice Hall, pag. 118: usamos para pasar a nuestro
tipo de fórmula que la aplicación (i,j) |-> n*i+j es una aplicación
inyectiva de {0,...,n}x{0,...,n-1} en |N).  Una vez generadas se hace
la unión de cláusulas con "palomar" y a lo que resulte se le puede
aplicar "satisfiable" o "unsatisfiable".  Con esta última función
tiene que dar "True" para todo n, eso es lo que asegura el Principio
del Palomar
-}

negativas :: Int -> [[Literal]]
negativas n = [[No(L(n*i+k)),No(L(n*j+k))] | j <- [1..n], i<- [0..j-1], k <- [0..n-1]]

positivas :: Int -> [[Literal]]
positivas n = [[L(i*n+j) | j <- [0..n-1]] | i <- [0..n]]

palomar :: Int -> [[Literal]]
palomar n = concatenate [positivas n, negativas n]

{- 
La función unsatisfiable (palomar n) tarda:

para n=1,   0'00 seg;   0'00 seg. iMac;     0'00 lenovo x220i;          516480 bytes 
para n=2,   0'00 seg;   0'00 seg. iMac;     0'00 lenovo x220i;          551992 bytes
para n=3,   0'01 seg;   0'01 seg. iMac;     0'01 lenovo x220i;         1105528 bytes
para n=4,   0'04 seg;   0'03 seg. iMac;     0'10 lenovo x220i;         3915176 bytes
para n=5,   0'25 seg;   0'33 seg. iMac;     0'96 lenovo x220i;        34575976 bytes
para n=6,   2'63 seg;   3'73 seg. iMac;    10'88 lenovo x220i;       381240944 bytes
para n=7,  31'62 seg;  45,93 seg. iMac;   131,49 lenovo x220i;      4581754088 bytes
para n=8, 412'77 seg; 594,64 seg. iMac;  1719.51 lenovo x220i;     59271449008 bytes
-}  

{- n reinas en un tablero nxn -}

{- Dado un tablero de ajedrez de n filas y n columnas, se trata de
situar en él n reinas de forma que ninguna ataque a otra distinta -}

{- Numeramos filas y las columnas desde 0 hasta n-1. La casilla que se
encuentra en la fila i-ésima y columna j-ésima se corresponde con el
número n*i+j. De esta forma, a cada casilla le corresponde un único
número entre 0 y n^2-1 -}

{- Representaremos por el literal L(m) al hecho de que la casilla m esté
ocupada por una reina -}

{- row n i es una cláusula que expresa que en la fila i-ésima debe ir
una reina -}

row :: Int -> Int -> [Literal]
row n i = [L(n*i+j) | j <- [0..n-1]]

{- rowT n es una lista de cláusulas, que expresan que en cada fila debe
haber una reina -}

rowT :: Int -> [[Literal]]
rowT n = [row n i | i <- [0..n-1]]

{- column n i es una cláusula que expresa que en la columna j-ésima debe
ir una reina -}

column :: Int -> Int -> [Literal]
column n j = [L(n*i+j) | i <- [0..n-1]]

{- columnT n es una lista de cláusulas, que expresan que en cada columna
debe haber una reina -}

columnT :: Int -> [[Literal]]
columnT n = [column n j | j <- [0..n-1]]

{- Dadas dos casillas de una fila i (n*i+j y n*i+k, con j<k), la
cláusula [No(L(n*i+j)), No(L(n*i+k))] expresa que no puede haber dos
reinas en esas dos casillas. Si variamos i entre 0 y n-1, j entre 0 y
n-2 y k entre j+1 y n-1, obtenemos una lista de cláusulas que
significan que no puede haber dos reinas en la misma fila. Esto lo
hacemos con la función noRow -}

noRow :: Int -> [[Literal]]
noRow n = [[No(L(n*i+j)), No(L(n*i+k))] | i <- [0..n-1], j <- [0..n-2], k <- [j+1..n-1]]

{- Dada una columna j, dos casillas de esa columna serían n*i+j y n*k+j,
con i<k.  La cláusula [No(L(n*i+j)), No(L(n*k+j))] expresa que no
puede haber dos reinas en esas casillas. Variando j entre 0 y n-1, i
entre 0 y n-2 y k entre i+1 y n-1 obtenemos una lista de cláusulas que
significan que no puede haber dos reinas en la misma columna.  La
función noColumn construye esta lista de cláusulas -}

noColumn :: Int -> [[Literal]]
noColumn n = [[No(L(n*i+j)), No(L(n*k+j))] | j <- [0..n-1], i <- [0..n-2], k <- [i+1..n-1]] 

{- Dada una casilla c=n*i+j que no esté en la última fila ni en la
última columna (es decir, i<n-1 y j<n-1), para desplazarnos hacia la
derecha por la diagonal ascendente, vamos sumando al número que
representa la casilla múltiplos de 9 (pues cada desplazamiento supone
aumentar en 1 el número de la fila y el número de la columna en que
nos encontramos). La función NoDiagU nos da una lista de cláusulas que
representan que si una reina está en una casilla, no puede haber
ninguna reina en la diagonal ascendente en la que se encuentra ésta -}

noDiagU :: Int -> [[Literal]]
noDiagU n = [[No(L(n*i+j)), No(L(n*i+j+(n+1)*k))] | i <- [0..n-2], j <- [0..n-2], k <- [1..min (n-1-i) (n-1-j)]]

{- Para desplazarmos de una casilla c=n*i+j (que no esté en la primera
fila ni en la última columna) por la diagonal descendente, hemos de ir
restando múltiplos de 7, pues cada desplazamiento supone aumentar en 1
el número de la columna, y disminuir en 1 el número de la fila. La
función noDiagD nos da una lista de cláusulas que representan que si
una reina está en una casilla, no puede haber ninguna reina en la
diagonal descendente en la que se encuentra -}

noDiagD :: Int -> [[Literal]]
noDiagD n = [[No(L(n*i+j)), No(L(n*i+j-(n-1)*k))] | i <- [1..n-1], j <- [0..n-2], k <- [1..min i (n-1-j)]]

{- Con la función queen reunimos todas las condiciones del problema de las n reinas -}

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
Ejercicio 1 examen 04-09-12 para comprobar la implicación semántica:

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


-- ÚLTIMOS EJEMPLOS --

{- Ejemplo distributividad -}

ex00A :: Int -> Int -> Formula
ex00A n 0 = Fa n
ex00A n m = K (Fa (m+n)) (ex00A n (m-1))

ex00:: Int -> Int -> Formula
ex00 1 m = ex00A 1 m
ex00 n m = A (ex00A n m) (ex00 (n-1) m)

frege :: Formula
frege = C (C (Fa 1) (C (Fa 2) (Fa 3))) (C (C (Fa 1) (Fa 2)) (C (Fa 1) (Fa 3)))
