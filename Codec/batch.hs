import Tableau 
import System.Directory
import System.IO
import System.IO.Unsafe

resultToFile result = do
 --  result<-provePath path 
   out <- openFile "result2.txt" WriteMode
   hPutStrLn out result
   
format [] = []   
format (x:xs) = x ++ "\n" ++ format xs

provePath path = result 
	where ff = getDirectoryContents path
	      f = unsafePerformIO ff
	      fofFile = getFiles f
	      file = addPath fofFile path
              result = format (proveFiles file)

provePath2 path = result 
	where ff = getDirectoryContents path
	      f = unsafePerformIO ff
	      fofFile = getFiles f
	      file = addPath fofFile path
              result = format (proveFiles2 file)

isFOF :: String->Bool
isFOF x
	| last(x) == 'p' = True
	| otherwise = False

getFiles [] = []
getFiles (x:xs)
	| isFOF x = x:getFiles xs
	| otherwise = getFiles xs

addPath [] path= []
addPath (x:xs) path= (path ++ "/" ++ x) : addPath xs path

proveFiles [] = []
proveFiles (x:xs) =  ((drop 11 x) ++": "++(show (isTheoremFile x))) : proveFiles xs

proveFiles2 [] = []
proveFiles2 (x:xs) =  ((drop 11 x) ++": "++(show (isTheoremFile2 x))) : proveFiles2 xs
