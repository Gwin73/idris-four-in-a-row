module Utils
import Prelude.List as L
import Data.Vect as V

%access export

public export
Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n $ Vect m a

toList : Matrix m n elem -> List $ List elem
toList = L.toList . map L.toList

group : (Eq a) => List a -> List $ List a
group [] = []
group (x :: xs) = 
	let (ys, zs) = L.span (== x) xs in (x :: ys) :: (group $ assert_smaller (x :: xs) zs) -- Bad

splitAt' : (n : Nat) -> Vect (1 + n + m) elem -> (Vect n elem, elem, Vect m elem)
splitAt' Z (x :: xs) = ([], x, xs)
splitAt' (S k) (x :: xs) with (splitAt' k xs) 
	| (l, m, r) = (x :: l, m, r)

natToFin' : (n : Nat) -> (m : Nat) -> Maybe (Fin m, LT n m) -- Is there a better way to do this?
natToFin' Z (S x) = Just (FZ, LTESucc $ LTEZero)
natToFin' (S k1) (S k2) with (natToFin' k1 k2)
	| Just (x, p) = Just (FS x, LTESucc p)
	| Nothing = Nothing
natToFin' _ _ = Nothing

plusMinusNeutral : {n : Nat} -> {m : Nat} -> (p : GTE m n) -> (n + (minus m n)) = m
plusMinusNeutral {n = Z} {m = m} _ = minusZeroRight m
plusMinusNeutral {n = (S _)} {m = Z} LTEZero impossible
plusMinusNeutral {n = (S _)} {m = Z} (LTESucc _) impossible
plusMinusNeutral {n = (S k1)} {m = (S k2)} p = 
	eqSucc (k1 + (minus k2 k1)) k2 (plusMinusNeutral {n = k1} {m = k2} $ fromLteSucc p)

succMinus : {n : Nat} -> {m : Nat} -> (p : GTE n m) -> (1 + minus n m) = (minus (1 + n) m) 
succMinus {n = Z} {m = Z} _ = Refl
succMinus {n = Z} {m = (S _)} LTEZero impossible
succMinus {n = Z} {m = (S _)} (LTESucc _) impossible
succMinus {n = (S k)} {m = Z} p = Refl
succMinus {n = (S k1)} {m = S (k2)} p = succMinus {n = k1} {m = k2} (fromLteSucc p)

private
lemma : {n : Nat} -> {x : Maybe $ elem} -> {xs : Vect n $ Maybe $ elem} -> LTE (fst $ catMaybes $ x :: xs) (S $ fst $ catMaybes $ xs)
lemma {n = Z} {x = Nothing} {xs = []} = LTEZero
lemma {n = Z} {x = (Just x)} {xs = []} = LTESucc LTEZero
lemma {n = (S len)} {x = Nothing} = lteSuccRight $ lteRefl
lemma {n = (S len)} {x = Just x} = ?l -- No idea how to prove this in Idris! The proof involves a case expression.

catMaybesLTE : {n : Nat} -> {xs : Vect n (Maybe elem)} -> LTE (fst $ catMaybes xs) n
catMaybesLTE {n = Z} {xs = []} = LTEZero
catMaybesLTE {n = (S len)} {xs = (x :: xs)} = 
	lteTransitive lemma $ LTESucc $ catMaybesLTE {n = len} {xs = xs}
