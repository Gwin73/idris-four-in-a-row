module Main
import Data.Vect as V
import Prelude.List as L
import Prelude.Basics as B
import Data.String as S
import Utils as U

%default total

data Player = X | O

other : Player -> Player
other X = O
other O = X

Show Player where
	show X = "X"
	show O = "O"

Eq Player where
	X == X = True
	O == O = True
	_ == _ = False	

record Board where 
	constructor MkBoard
	columns : Matrix 7 7 $ Maybe Player

rows : Board -> Matrix 7 7 $ Maybe Player
rows = transpose . columns

Show Board where
    show = unlines . map (concat . map (maybe "." show)) . L.toList . rows

diagonals1 : Board -> List $ List $ Maybe Player
diagonals1 board = map catMaybes 
                 $ transpose 
                 $ zipWith (++) (take 7 $ iterate (Nothing::) []) (map (map Just) $ U.toList $ columns board)

diagonals2 : Board -> List $ List $ Maybe Player
diagonals2 = diagonals1 . MkBoard . transpose . columns

draw : Board -> Bool
draw = all (all isJust) . rows
	
winner : Board -> Maybe Player 
winner board = head'
             $ catMaybes 
	         $ mapMaybe head' -- Is there a better way to handle the impossible case [] with a proof?
			 $ L.filter (\x => L.length x >= 4)
			 $ concatMap {t = List} {a = List $ Maybe Player} group
			 $ concatMap (\ f => f board) {t = List} {a = Board -> List $ List $ Maybe Player}
			 $ [U.toList . rows, U.toList . columns, diagonals1, diagonals2]

legalMove : (n : Nat) -> Board -> Maybe $ LTE n 6
legalMove n board with (natToFin' n 7)
	| Nothing = Nothing
	| Just (f, p) = map (\ _ => fromLteSucc p) (V.index f $ V.head $ rows board)
	
dropColumn : Player -> Vect 7 $ Maybe Player -> Vect 7 $ Maybe Player
dropColumn player column = 
	let tmp = V.catMaybes $ (Just player) :: (tail column) in 
	let n = fst tmp in
	let xs = snd tmp in
	let p1 = catMaybesLTE {xs = (Just player) :: (tail column)} in
	let p2 : ((minus 7 n) + n = 7) = rewrite plusCommutative (minus 7 n) n in plusMinusNeutral p1 in
	rewrite sym p2 in
	(replicate (minus 7 n) Nothing) ++ (map Just xs)

move : Player -> Nat -> Board -> Maybe Board
move player n board with (legalMove n board)
    | Nothing = Nothing
    | Just p = Just board' where 
    	tmp : (Vect n $ Vect 7 $ Maybe Player, Vect 7 $ Maybe Player, Vect (minus 6 n) $ Vect 7 $ Maybe Player)
    	tmp = splitAt' n $ rewrite plusMinusNeutral p in columns board

    	board' = let (left, column, right) = tmp in 
    		MkBoard $ 
    		replace {P = \n => Matrix n 7 $ Maybe Player} (plusMinusNeutral $ lteSuccRight p) $ 
			rewrite sym $ succMinus p in 
	        left ++ [dropColumn player column] ++ right

record Game where
	constructor MkGame
	player : Player
	board : Board

partial gameloop : Game -> IO ()
gameloop game@(MkGame player board) = do
    putStr $ show player ++ "s turn: "
    line <- getLine
    case (parsePositive line) >>= (\n => move player n board) of
        Nothing => (print board) >>= (\_ => gameloop game)
        Just board' => do
            print board'
            if draw board
                then putStrLn "Draw!"
                else case winner board' of
                    Just player => putStrLn $ show player ++ " Won!"
                    Nothing => gameloop $ MkGame (other player) board'

partial main : IO ()
main = do
    let board = MkBoard (replicate 7 $ replicate 7 Nothing)
    print board
    gameloop $ MkGame X board