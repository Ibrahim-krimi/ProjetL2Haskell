----- Krimi Ibrahim , num.etu: 22011592 , groupe:4b-----
type Var = Char

data Litteral = Pos Var | Neg Var | Null -- j ai ajouter un variable null dans la litteral car j ai pas trouve comment je pourrai arrete le programme dans le cas ou la litteral est vide.
	deriving (Show, Eq)

type Clause = [Litteral]

type Formule = [Clause]

type Distribution = [(Var, Bool)]

testClause = [Pos 'a',Pos 'b',Neg 'a',Pos 'd',Neg 'f']

f1 = [[Pos 'a', Pos 'b'], [Neg 'a', Neg 'b'], [Pos 'a', Neg 'b']]
f2 = [[Pos 'a', Pos 'c', Neg 'b'], [Pos 'a', Neg 'c'], [Neg 'a', Pos 'b', Neg 'c'], [Neg 'a', Neg 'b']]
f3 = [[Pos 'a', Pos 'b'], [Pos 'a', Neg 'b'],[Neg 'a', Pos 'b'], [Neg 'a', Neg 'b']]
f4 = [[Pos 'a', Pos 'c', Neg 'b'], [Pos 'a', Neg 'c', Pos 'b'], [Neg 'a', Pos 'b', Neg 'c'],[Neg 'a', Neg 'b']]
f5 = [[Pos 'a', Pos 'b'], [Pos 'a', Neg 'b'], [Neg 'a', Pos 'b'], [Neg 'a', Neg 'b']]
f6 = [[Pos 'a', Neg 'a'], [Pos 'c'], [Neg 'a', Pos 'b', Neg 'c'], [Pos 'a', Neg 'b'],[Pos 'a', Pos 'c'], [Pos 'a', Pos 'b', Neg 'c']]
fp = [[Pos 'b',Neg 'a'],[Pos 'c',Neg 'b'],[Neg 'a',Pos 'b',Neg 'c'],[Pos 'b',Pos 'c']]

---------------DM Partie 1-----------------------------
--1)
--a 
listeVarsClause :: Clause -> String
listeVarsClause [] = ""
listeVarsClause (Neg a:xs) = a : listeVarsClause xs
listeVarsClause (Pos a:xs)= a : listeVarsClause xs



--b
listeVarsFormule :: Formule -> String
listeVarsFormule [] = ""
listeVarsFormule (x:xs) = listeVarsClause x ++ listeVarsFormule xs


--c
rmdups :: Eq a => [a] -> [a]
rmdups [] = []
rmdups (x:ys)
	| elem x ys = rmdups ys
	| otherwise = x : (rmdups ys)


listeVars :: Formule -> String
listeVars cs = rmdups (listeVarsFormule cs)


--2) 
--a
valeur :: Litteral -> Distribution -> Bool
valeur _ [] = True
valeur (Pos a) ((x,y):xs) 
	| a==x = y==True
	| otherwise = valeur (Pos a) xs
valeur (Neg a) ((x,y):xs)
	| a==x = y==False 
	| otherwise = valeur (Neg a) xs
	


--b
evalue :: Formule -> Distribution -> Bool
evalue xs xy = and [ or[valeur litteral xy | litteral <- clause] | clause <-xs]

--3)
genereTable :: [Var] -> [Distribution]
genereTable [] = [[]]
genereTable (x:xs) = map ((x, True):) (genereTable xs) ++ map ((x, False):) (genereTable xs)

--(a) LA longueur length generTable vs si vs est une liste de n variables est de de 2^n


--(b)
sontStatis :: Formule -> [Distribution] 
sontStatis xs = [ x | x <- genereTable(listeVars xs),evalue xs x ==True]
	
--(c) 
ratio :: Formule -> Float 
ratio [] = 0.0
ratio f = fromIntegral(length(sontStatis f)) / fromIntegral(length(genereTable(listeVars f)))
--------------------DM Partie 2--------------------------


--2. Prétraitement : Suppression des tautologies
--3. Définir la fonction (negation lit) qui à un littéral associe sa négation 
negation :: Litteral -> Litteral
negation (Neg y) = (Pos y) --si x est un variable negative alor on le change en variable positive
negation (Pos y) = (Neg y) --si x est un variable positive alor on le change en variable negative

--4. Définir la fonction (estTauto ls)
estTauto :: Clause -> Bool
estTauto [] = False -- false*
estTauto (y:ys) 
	| elem (negation y) ys = True -- encherche le elemnt x dans le reste de la liste xs si on le trouve on envoye True  
	| otherwise = estTauto ys -- sinon on fait l appele recursive sur le reste si il arrive a la fin de la liste sans le prog va envoye false*
	
elimineTauto :: Formule -> Formule
elimineTauto = filter (not . estTauto)


--3. Existence d’une distribution : mise en œuvre de DPLL (v1)
--3.1 Conditions d’arrêt

--2 Définir la fonction (estUnitaire c) qui détermine si une clause c est unitaire
estUnitaire :: Clause -> Bool
estUnitaire [] = False --on test si la fonction est vide
estUnitaire (x:xs) 
	| xs==[] = True -- si le reste de la fonction est vide alors ce une clause unitaire 
	| otherwise = False -- sinon le reste est remplis alors c nest pas une clause unitaire


--3. Compléter la définition de la fonction (estEvidtContradic cs).
clauseNeg :: Clause -> Clause
clauseNeg [] = []
clauseNeg (x:xs) = negation x : clauseNeg xs

estEvidtContradic :: Formule -> Bool
estEvidtContradic [] = False -- si la formue est vide en envoye faux et aussi une condtition pour areter le prog.
estEvidtContradic (x:xs) 
	| estUnitaire x && elem (clauseNeg x) xs = True -- si la clause x est unitaire  et il existe son variavle negative dans le reste on envoye True
	| otherwise = estEvidtContradic xs -- sinon en fait l appele recurisve sur le reste jusque la fin de la liste (liste vide).


--3.2 Simplification : règle du littéral seul (ou règle de la clause unitaire)
--2. Définir les fonctions (existeSeul cs) et (trouveSeul cs)
existeSeul :: Formule  -> Bool 
existeSeul [] = False -- si la formule est vide en envoye faux et aussi une condtition pour areter le prog.
existeSeul ((x:ys):xs) --sinon 
	|ys==[] = True-- si le reste de la clause est vide ys alors en envoye True 
	|otherwise = existeSeul xs--sinon on fait l appelle recursive sur le reste de la formule
     
trouveSeul :: Formule  -> Litteral
trouveSeul [] = Null --si la formule est vide alors en evoye Null , null ce un variable qui je vien de la ajouter car j ai pas trouve comment je pourrai arrete le programme dans le cas ou la litteral est vide.
trouveSeul ((x:ys):xs)
	|ys==[] = x -- si le reste de la clause est vide ys alors en envoye le premie valeur x 
	|otherwise = trouveSeul xs --sinon on fait l appelle recursive sur le reste de la formule



--3. Définir la fonction (elimineSeul cs l)

elimineSeul :: Formule -> Litteral -> Formule -- elle prend une formule , litteral , et elle envoye un formule
elimineSeul [] l = [] -- si le formule est vide  on envoye une liste vide (condtion d arete de prog)
elimineSeul (c:cs) l--sinon
	|elem l c = elimineSeul cs l -- si le literal l existe dans clause c alors on fait l appele sur le reste  de la formule 
	|elem (negation l) c = [ y | y <- c ,(negation l) /= y] : (elimineSeul cs l) -- si la negation de l existe dans c  alors on elimine le de la caluse 
    	|otherwise = c : elimineSeul cs l -- siinon on l ajoute dans le clause dans la formule et on continue sur le reste de la liste 
    	
    	
--3.3 Simplification : règle du littéral pur

--2. Définir les fonctions (existePur cs) et (trouvePur cs) ainsi que la fonction (eliminePur cs l)



exist :: Formule -> Litteral -> Bool
exist [] _ = True  -- si la formule est vide on envoye True
exist (x:xs) litt  -- sinon 
	| elem litt x = False-- si liit existe dans la clause x alors on evloye false
	| otherwise = exist xs litt-- sinon  on fait l appele recursive 

arrayPur :: Formule -> [Litteral]
arrayPur f = [  litt |  c <- f, litt <- c  ,exist f (negation litt)] -- on mait tous les litteralpur dans un liste  arraypur pour que on l appele dans la fonction existePur


existePur :: Formule -> Bool
existePur xs = length (arrayPur xs) /= 0 -- si la liste est n est pas  vide(longeur de la liste !=0) alors on envoye true de la fonction exist , sinon on envoye false 

trouvePur :: Formule -> Litteral
trouvePur [] = Null -- si la formule est vide on envoye null
trouvePur xs = head(arrayPur xs)--sinon on prend le premeir element de la liste envoye de la fonction arrayPur xs 

eliminePur :: Formule -> Litteral -> Formule  
eliminePur [] _ = [] ---- si la formule  est vide et meme s il y a  une Litteral dans le deuxieme parametre  on ajoute une liste vide (condtion pour areter le programme)
eliminePur (x:xs) litt ---- si la formule   ne est pas vide 
	| elem litt x = eliminePur xs litt -- si le litteral existe dans la clause x alors on pass a la clause suivant (appele recursive ) , sa veut dire on ecrase l elemnt x
	| otherwise = x : eliminePur xs litt -- sinon on ajoute la clause x dans la formule x


--3.4 Recherche exhaustive
-- cette fonction permet de déterminer si une formule est satisfaisable en appliquant estSatis sur la formule sans tautologie
dpll :: Formule -> Bool
dpll = estSatis . elimineTauto	

estSatis :: Formule -> Bool
estSatis [] = True -- si la formule est vide alors elle est satisfaisable ( aussi la condition pour arreter le prog)
estSatis f
	| estEvidtContradic f = False-- si la formule est contradictoire on retourne false  sa veut dire la formule est insatisfaisable
	| existeSeul f = estSatis (elimineSeul f (trouveSeul f)) -- s il y a  un Litteral seul dans la formule alors on applique la regle du Litteral seul sur la formule et  on fait travail l appelle recursive
	| existePur f =  estSatis (eliminePur f (trouvePur f)) -- s il il y a  un Litteral pur dans la formule alors on applique la regle du Litteral pur sur la formule et  on fait travail l appelle recursive
	| otherwise = if estSatis (elimineSeul f (head (head f))) then True else estSatis (elimineSeul f (negation (head (head f))))
	-- sinon on applique le  Recherche exhaustive avec  le premier Litteral de la formule et si la formule resultat f1 est satisfaisable on retourne true , et si f1 n'est pas satisfaisable on applique le Recherche exhaustive  sur la négation du premier Litteral de la formule et on tester si la formue resultat f2 est satisfaisable ou pas .
	   
	   
--4. (BONUS)

--4
associe :: Litteral -> (Var, Bool)
associe (Pos c) = (c, True)
associe (Neg c) = (c, False)

dpllBis :: Formule -> Distribution
dpllBis f = if (estSatis f) then (calculDistri f) else []

calculDistri :: Formule -> Distribution
calculDistri [] = []
calculDistri f
	| existeSeul f = associe (trouveSeul f) : calculDistri (elimineSeul f (trouveSeul f))
	| existePur f = associe (trouvePur f) : calculDistri (eliminePur f (trouvePur f))
	| otherwise = if estSatis (elimineSeul f (head (head f))) then associe (head (head f)) : calculDistri (elimineSeul f (head (head f))) else associe (negation (head (head f))) : calculDistri (elimineSeul f (negation (head (head f))))
		   
	   
	
	
