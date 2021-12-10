module Final where

-- helpers:
-- liftA :: (a -> b) -> [a] -> [b]
-- liftA2 :: (a -> b -> c) -> [a] -> [b] -> [c]
-- liftA3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
import Control.Applicative(liftA, liftA2, liftA3)
import Data.List


-- FSA-to-RegExp conversion
-- Important: consider the states 0 and -1 to be reserved for the initial and final states of a gfsa
-- reference: https://courses.engr.illinois.edu/cs373/fa2010/Lectures/lect07.pdf 


-- DFA/FSA
type Automaton st sy = ([st], [sy], [st], [st], [(st,sy,st)])

-- Generalized Nondeterministic Finite Automata
    -- key difference from FSA: 
        -- Transitions are in the form of Regexes rather than a single symbol
        -- Only contains a single initial and a single accept state
        -- Every state (aside from the initial and final states) has a transition to every other state
        -- Every state implicitly has a transition of OneRE to itself
        -- A transition of ZeroRE implies no path

-- Q: states
-- Sigma: alphabet
-- i: initial state (0)
-- f: final state (-1)
-- delta: transitions (in the form of regex)
type GeneralizedAutomaton st sy = ([st], [sy], st, st, [(st, RegExp sy, st)])

data RegExp a = Lit a | Alt (RegExp a) (RegExp a) | Concat (RegExp a) (RegExp a) 
              | Star (RegExp a) | ZeroRE | OneRE
              deriving (Eq,Show)



---------------------------------------
-- Sample FSA/DFAs 

dfa1 :: Automaton Int Char
dfa1 = ([1,2,3], ['a', 'b', 'c'], [1], [3], [(1,'a',2), (1,'b',1), (2, 'c', 3)])

dfa2 :: Automaton Int Char
dfa2 = ([1], ['a', 'b', 'c'], [1], [1], [(1,'a',1), (1,'b',1), (1, 'c', 1)])


---------------------------------------
-- Helpers for combining RegExps 
    -- performs some type checks to shorten expressions when possible

concatHelper :: (Eq sy) => RegExp sy -> RegExp sy -> RegExp sy
concatHelper r1 r2 =
    case ((r1 == ZeroRE) || (r2 == ZeroRE)) of
        True -> ZeroRE
        False -> case (r1 == OneRE) of
                    True -> r2
                    False -> case (r2 == OneRE) of
                                True -> r1
                                False -> (Concat r1 r2)


starHelper :: (Eq sy) => RegExp sy -> RegExp sy
starHelper r1 =
    case ((r1 == ZeroRE) || (r1 == OneRE)) of
        True -> r1
        False -> Star r1


unionHelper :: (Eq sy) => RegExp sy -> RegExp sy -> RegExp sy
unionHelper r1 r2 =
    case (r1 == ZeroRE) of
        True -> r2
        False -> case (r2 == ZeroRE) of
                    True -> r1
                    False -> (Alt r1 r2)


---------------------------------------
-- Part 1: Convert DFA/FSA to GNFA

-- converts a list of regular expresions into a single unionized regex
unionizeList :: (Eq sy) => [RegExp sy] -> RegExp sy
unionizeList r_list = 
    case r_list of
        [] -> ZeroRE
        x:[] -> x
        x:rest -> (unionHelper x (unionizeList rest))


combinations :: [a] -> [a] -> [(a,a)]
combinations list1 list2 = 
    (liftA2 (\q1 -> \q2 -> (q1, q2)) list1 list2)


-- given delta, q1 and q2, find all of the transitions corresponding to the pair and create a Regex from them
formatTransitions :: (Eq st) => (Eq sy) => [(st, sy, st)] -> (st, st) -> RegExp sy
formatTransitions delta (q1, q2) =
    let list = (filter (\(a, sym, b) -> ((a == q1) && (b == q2))) delta) in
    let rList = (map (\(a,q,b) -> Lit q) list) in
    let reg = (unionizeList rList) in
    case ((reg == ZeroRE) && (q1 == q2)) of 
        True -> OneRE 
        False -> reg

-- convert a DFA into a GFSA
dfaToGFSA :: (Eq sy) => Automaton Int sy -> GeneralizedAutomaton Int sy
dfaToGFSA dfa =
    let (q, sigma, i, f, delta) = dfa in 
    let q' = q ++ 0:(-1):[] in
    let sigma' = sigma in
    let i' = 0 in
    let f' = -1 in
    let initTransitions = (map (\q0 -> (0, OneRE, q0)) i) in
    let finTransitions = (map (\q0 -> (q0, OneRE, -1)) f) in
    let allStateCombos = (combinations q q) in
    let transitions' = (map (\(q1, q2) -> (q1, (formatTransitions delta (q1,q2)), q2)) allStateCombos) in
    let delta' = initTransitions ++ finTransitions ++ transitions' in
    (q', sigma', i', f', delta')



---------------------------------------
-- Part 2: Convert GNFA into RegExp

-- helper function to find the RegExp associated with start state q1 and end state q2
-- returns OneRE if no transition is found and q1 and q2 are the same state
-- returns ZeroRE if no transition is found otherwise
findTransition :: (Eq st) =>  [(st, RegExp sy, st)] -> st -> st -> RegExp sy
findTransition delta q1 q2 =
    case delta of
        [] -> case (q1 == q2) of {True -> OneRE; False -> ZeroRE}
        (a, reg, b):rest -> case ((a == q1) && (b == q2)) of
                                True -> reg
                                False -> (findTransition rest q1 q2)


combineRegex :: (Eq sy) => RegExp sy -> RegExp sy -> RegExp sy -> RegExp sy -> RegExp sy
combineRegex r1 r2 r3 r4 =
    unionHelper (concatHelper (r1) (concatHelper (starHelper r2) r3)) r4



-- rip out a single state
-- sigma, i and f stay the same
gfsaRip :: (Eq sy) => GeneralizedAutomaton Int sy -> GeneralizedAutomaton Int sy
gfsaRip gfsa =
    let (q, sigma, i, f, delta) = gfsa in
    let q' = (filter (\q1 -> ((q1 /= 0) && (q1 /= -1))) q) in
    case q' of
        [] -> gfsa
        qStar:rest -> let q'' = (delete qStar q) in
                    let statePairs = (combinations (delete (-1) q'') (delete 0 q'')) in
                    let formatTransition = (\(q1, q2) -> let r1 = (findTransition delta q1 qStar) in
                                                        let r2 = (findTransition delta qStar qStar) in
                                                        let r3 = (findTransition delta qStar q2) in 
                                                        let r4 = (findTransition delta q1 q2) in
                                                        (q1, (combineRegex r1 r2 r3 r4), q2)
                                            ) in
                    let delta' = (map formatTransition statePairs) in
                    (q'', sigma, i, f, delta')
  


-- convert from FSA/DFA to GFSA and then from GFSA to Regex
gfsaToRe :: (Eq sy) => GeneralizedAutomaton Int sy -> RegExp sy
gfsaToRe gfsa = 
    let (q, sigma, i, f, delta) = gfsa in
    case ((length q) <= 2) of
        True -> findTransition delta 0 (-1)
        False -> gfsaToRe (gfsaRip gfsa)



-- final function
-- convert dfa to regex
dfaToRe :: (Eq sy) => Automaton Int sy -> RegExp sy
dfaToRe dfa =
    (gfsaToRe (dfaToGFSA dfa))


