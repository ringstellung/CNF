module Formulas (module Formulas) where

{- Definimos el tipo de dato Formula, que refleja la escritura de las formulas en forma polaca. 
Las fórmulas atóminas están basadas en números enteros (Int). -}

data Formula = Fa Int 
             | C Formula Formula 
             | E Formula Formula 
             | K Formula Formula 
             | N Formula 
             | A Formula Formula
               deriving (Eq, Ord)

{-
Varias fórmulas para hacer pruebas
-}

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

{-
y1 = se x
y2 = sc y1
y3 = ing y2
y4 = dak y3
y5 = dak y4
y6 = aa y5
y7 = aa y6
-}



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


{- Crea una fórmula formada únicamente por conjunciones -}

f :: Int -> Int -> Formula
f 0 n = K (Fa n) (N (Fa n))
f m n = K (f (m -1) n) (f (m-1) (n+2^m))


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

