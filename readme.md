# Implementaciones del Algoritmo CNF y D&P 

Contiene un código en `Haskell` que implementa la obtención de dada
una fórmula proposicional una forma normal conjuntiva suya.

La siguiente lista representa un elenco de funciones involucradas en
el código:

1. La fnc:

		clausularform :: Formula -> Formula

1. El algoritmo de subsumisión (número limitado de variables):

		sieveClauseList :: [Ic] -> [Ic]

1. Transformar una fórmula y con conjunto de fórmulas en un conjunto
de cláusulas:

		form2claus :: Formula -> [[Literal]]
		setform2clausImp :: [Formula] -> [[Literal]]

1. El algoritmo de Davis&Putnam:

		unsatisfiable:: [[Literal]] -> Bool
		satisfiable :: [[Literal]] -> (Bool, [Literal])

1. El teorema de la deducción:

		deductionTheorem :: [Formula] -> Formula -> [Formula]

1. La implicación semántica:

		sImplies :: [Formula] -> Formula -> Bool
		extsImplies :: [Formula] -> Formula -> (Bool,[Literal])

1. Reconocer si una fórmula es una tautología o no:

		tautological :: Formula -> Bool

1. Reconocer si dos fórmulas son equivalentes o no:

		isLogEquiv :: Formula -> Formula -> Bool


Matizamos algo más:

1. `distribute`: aplica `dak` las veces necesarias para llegar a la forma
clausular. Usa la función `alternancia` que mide el número mínimo
de veces que es necesario aplicarla.

1. `asociate`: aplica la función `aka` a una fórmula en forma clausular
el mínimo número de veces necesario para que todas las conjunciones y
disyunciones estén asociadas por la izquierda.

1. `clausularform`: aplica las funciones anteriores en el orden adecuado
para transformar una fórmula en otra equivalente a ella que esté en
forma clausular.

1. `form2claus`: Dada una formula, la función `form2claus` extrae sus
cláusulas. Elimina las cláusulas tautológicas y los literales
repetidos de cada una de las cláusulas.

1. `setform2claus`: Dado un conjunto (lista) de fórmulas, extrae sus cláuslas. 
Elimina las cláusulas tautológicas y los literales repetidos en cada una 
de las cláusulas.

1. `insatisfiable`: Dado una lista de cláusulas, devuelve `True`
o `False` dependiendo de si el conjunto de cláusulas es insatisfacible o
no lo es. Para ello hace uso del algoritmo de Davis&Putnam.

1. satisfiable: Dada una lista de cláusulas, devuelve `True` o `False`
dependiento de si el conjunto de cláusulas es satisfacible o no. En
caso de ser satisfacible, da una lista de literales, que al
interpretalos como verdaderos, satisface al conjunto; caso de ser
insatisfacible, da la lista vacía.

1. `form2claus`: Hace lo mismo que `setform2claus`.

1. `sImplies`: Dado un conjunto de fórmulas, y una fórmula, dice si
ésta es consecuencia lógica del conjunto de fórmulas.

1. `extsImplies`: Igual que el anterior, salvo que en el caso de que la
implicación sea falsa nos da además una lista de literales que nos
muestra por qué la implicación es falsa.
