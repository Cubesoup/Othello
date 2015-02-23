-- Written by Chad Nester in 2015 for teaching purposes at the University of Calgary.
--
-- This file contains a fast representation of an othello game board, as well as
-- the ability to check the legality of a move relative to a board state, the
-- ability to update the board with the effects of a legal move, two toy strategies,
-- and a function to have two strategies play one another.

import Data.Word
import Data.Bits
import Prelude hiding (flip)

{- representation -}

-- The board is represented as two 64-bit words, with the nth bit of each
-- word corresponding to the nth position on the othello board according
-- to the following numbering scheme:
{-
 00 01 02 03 04 05 06 07
 08 09 10 11 12 13 14 15
 16 17 18 19 20 21 22 23
 24 25 26 27 28 29 30 31
 32 33 34 35 36 37 38 39
 40 41 42 43 44 45 46 47
 48 49 50 51 52 53 54 55
 56 57 58 59 60 61 62 63
-}

--            empty? white? (nth bit set if yes, not set if no)
type Board = (Word64,Word64)

emptyBoard :: Board
emptyBoard = (0xFFFFFFFFFFFFFFFF,  -- every position is empty
              0x0000000000000000)  -- no position contains a white piece

initialBoard :: Board
initialBoard = replace
               (replace
                (replace
                 (replace emptyBoard White 27) Black 28) Black 35) White 36

-- We display the board as a grid               

display :: Board -> String
display (empty, white) = ' ' : ((spaces . newlines) (map getCellChar [0..63]))
  where
    getCellChar :: Posn -> Char
    getCellChar pos = if testBit empty pos then '_'
                         else if testBit white pos then 'W'
                                 else 'B'

-- intersperse spaces horizontally between board positions
spaces :: [Char] -> [Char]
spaces [] = []
spaces (x:xs) = x : ' ' : (spaces xs)

-- put a newline every 8 elements
newlines :: [Char] -> [Char]
newlines [] = ['\n']
newlines xs = (take 8 xs) ++ ['\n'] ++ (newlines (drop 8 xs))


{- game logic (move legality checking) -}

type Posn = Int -- the idea being that the Int is between 0 and 63

type Cell = Maybe Colour

data Colour = Black | White
  deriving (Show, Eq)

op :: Colour -> Colour
op Black = White
op White = Black
  

-- get the thing "at" a give position, (board `at` posn) is nice...
at :: Board -> Posn -> Cell
at b p = if (testBit (fst b) p) then Nothing
            else 
              case testBit (snd b) p of
                True  -> Just White
                False -> Just Black
                   

-- we define one function for each direction a capture could occur in
-- from a given board position. These directions will return the position
-- one space away in the appropriate direction on the board, or Nothing
-- if moving in that direction would take us off the edge of the board.                

type Direction = Posn -> Maybe Posn

up :: Posn -> Maybe Posn
up x = if x < 8 then Nothing else Just $ x - 8

down :: Posn -> Maybe Posn
down x = if x > 55 then Nothing else Just $ x + 8

left :: Posn -> Maybe Posn
left x = if x `mod` 8 == 0 then Nothing else Just $ x - 1

right :: Posn -> Maybe Posn
right x = if x `mod` 8 == 7 then Nothing else Just $ x + 1

up_right :: Posn -> Maybe Posn
up_right x = return x >>= up >>= right

up_left :: Posn -> Maybe Posn
up_left x = return x >>= up >>= left

down_right :: Posn -> Maybe Posn
down_right x = return x >>= down >>= right

down_left :: Posn -> Maybe Posn
down_left x = return x >>= down >>= left

directions :: [Direction]
directions = [up,down,left,right,up_right,up_left,down_right,down_left]

-- we next develop the ability to detect capture in a given direction.

-- get the pieces hit by a "ray" cast in the given direction
-- from the given position. (does not include the initial position).
probe :: Board -> Posn -> Direction -> [Cell]
probe brd pos dir = case dir pos of
                        Nothing   -> []
                        Just pos' -> (brd `at` pos') : probe brd pos' dir

-- we check whether or not the list returned by the probe is a capture
analyze :: Colour -> [Cell] -> Bool
analyze _ []     = False -- the piece is next to the edge in this direction
analyze c (x:xs)
  | x == Nothing       = False -- the next space is empty, so no capture
  | x == (Just c)      = False -- need at least one enemy piece in the middle
  | x == (Just (op c)) = analyze' c xs -- potential capture!
  
analyze' :: Colour -> [Cell] -> Bool
analyze' c [] = False
analyze' c (x:xs)
  | x == Nothing       = False -- empty spaces still no good
  | x == (Just c)      = True  -- a capture!
  | x == (Just (op c)) = analyze' c xs -- the line goes on...                   


-- detecting whether or not a position is a valid move for a colour is
-- now simply a matter of checking that it is empty, and ensuring that
-- at least one capture will result.

legal :: Board -> Colour -> Posn -> Bool
legal brd col pos = ((brd `at` pos) == Nothing) && 
                    (or $ map ((analyze col) . (probe brd pos)) directions)


legal_moves :: Board -> Colour -> [Posn]
legal_moves brd col = [mv | mv <- [0..63],
                            legal brd col mv]

                      
-- we also need the ability to make a move on the board. We will asuume
-- any move given to this function as input is a legal move.

make_move :: Board -> Colour -> Posn -> Board
make_move brd col pos = foldr consf (replace brd col pos) directions
  where
    consf = (\dir board -> flip board col pos dir)


flip :: Board -> Colour -> Posn -> Direction -> Board
flip brd col pos dir = if analyze col (probe brd pos dir)
                          then flip' brd col ((\(Just x) -> x) (dir pos)) dir
                          else brd     

flip' :: Board -> Colour -> Posn -> Direction -> Board  
flip' brd col pos dir
  | piece == (op col) = flip' (replace brd col pos) col next dir
  | piece == col      = brd
  where
    piece = (\(Just x) -> x) (brd `at` pos)
    next = (\(Just x) -> x) (dir pos)


replace :: Board -> Colour -> Posn -> Board
replace brd col posn = (clearBit (fst brd) posn,
                        case col of
                          White -> setBit (snd brd) posn
                          Black -> clearBit (snd brd) posn)




{- Our Strategies -}


type Strategy = Board -> Colour -> Maybe Posn -- Nothing represents a pass.


-- only two strategies are included, lazyStrategy and lazyStrategy', which
-- are symmetric in the sense that you can only get two unique (in terms of
-- final scoring) games with them.

lazyStrategy :: Strategy
lazyStrategy board col = if moves == [] then Nothing
                            else Just $ head moves                                   
  where
    moves = legal_moves board col

lazyStrategy' :: Strategy
lazyStrategy' board col = if moves == [] then Nothing
                             else Just $ last moves
  where
    moves = legal_moves board col


{- Now, we can write the "game loop" -}


-- no move legality checking is done, as all of the strategies here
-- do that internally. If this were adapted to be a game server,
-- that would need to go in the "play" function.
game :: Strategy -> Strategy -> IO ()
game s1 s2 = do
      let black = (s1,Black)
          white = (s2,White)
      play black white initialBoard 

type Player = (Strategy, Colour)

-- the player to move comes before the other player
play :: Player -> Player -> Board -> IO ()  
play active inactive board = do
  putStrLn (display board)
  if (legal_moves board White == []) &&
     (legal_moves board Black == []) then score board
    else
      case (fst active) board (snd active) of
        Nothing -> if (legal_moves board (snd active)) == []
                      then play inactive active board
                           else putStrLn ("illegal pass by " ++ (show (snd active)))
        Just mv -> play inactive active (make_move board (snd active) mv)

score :: Board -> IO ()
score board = do
  putStrLn "The game is over, the scores are:"
  putStrLn $ "White: " ++ (show white_score)
  putStrLn $ "Black: " ++ (show black_score)
  putStrLn $ "The winner is ... " ++ (if white_score > black_score
                                       then "White"
                                       else if black_score > white_score
                                              then "Black"
                                              else "Nobody! The game is a tie.")     
  where 
    white_score = (popCount (snd board)) - (popCount (fst board))
    black_score = 64 - (popCount (snd board)) - (popCount (fst board))
