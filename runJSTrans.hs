module Main where
import System
import JSTrans.AST
import JSTrans.Parser as Parser
import JSTrans.Writer as Writer
import JSTrans.Transform as Transform
import IO (stderr,hPutStrLn)

main :: IO ()
main = do{ args <- getArgs
         ; (filename,source)
             <- case args of
                  (filename:_) -> fmap ((,) filename) $ readFile filename
                  [] -> fmap ((,) "<stdin>") $ getContents
         ; case parse Parser.program filename source of
             Left err -> hPutStrLn stderr $ "Parse Error: " ++ show err
             Right val ->
                 do{ let transformed = Transform.transformProgram transformAll val
                   ; let s = Writer.program transformed ""
                   ; putStrLn s
                   }
         }
