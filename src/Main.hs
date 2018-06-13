{-# OPTIONS_GHC -ddump-deriv #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.State
import Data.Fix
import Data.Foldable
import Data.Monoid
import Data.String
import Data.Text (Text, unpack)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Nix.Atoms
import Nix.Expr.Types
import Nix.Parser (Result(..), parseNixFile)
import Prelude hiding ((<$>))

{-
== Nix precedence table

* taken from https://gist.github.com/joepie91/c3c047f3406aea9ec65eebce2ffd449d
  but reversed for ergonomics
* "inside list" precedence added. this is one higher than function application
* lambda abstraction precedence context added as lowest

16 SELECT e.attrpath [or default value]
15 INLIST [ a b c ]
14 APP f arg1 arg2
13 NEG -e
12 HAS_ATTR e ? attrpath
11 CONCAT e1 ++ e2
10 MUL, DIV e1 * e2, e1 / e2
9 ADD, SUB e1 + e2, e1 - e2
8 NOT !e
7 UPDATE e1 // e2
6 LT, LTE, GT, GTE
5 EQ, NEQ
4 AND &&
3 OR ||
2 IMPL e1 -> e2
1 ABS x: y
-}
data PrinterState = PrinterState
    { pageWidth :: Int
    , column :: Int
    , line :: Int
    , indent :: Int
    , buffer :: Text
    , precedence :: Int
    } deriving (Show)

defaultState = PrinterState 60 0 0 0 "" 0

render s = buffer $ execState s defaultState

withPrec p =
    wrap
        (\s -> s {precedence = p})
        (\oldst newst -> newst {precedence = precedence oldst})

wrap :: Monad m => (s -> s) -> (s -> s -> s) -> StateT s m a -> StateT s m a
wrap f restore m = do
    st <- get
    let newSt = f st
    put newSt
    r <- m
    modify (restore st)
    return r

hsep = interp space

hcat = interp (return ())

vcat = interp writeLine

writeNoNl txt =
    modify (\p -> p {column = column p + T.length txt, buffer = buffer p <> txt})

write txt
    | T.all (/= '\n') txt = writeNoNl txt
    | otherwise = interp writeLine (map writeNoNl $ T.splitOn "\n" txt)

writeLine =
    modify
        (\p ->
             p
                 { column = 0
                 , line = line p + 1
                 , buffer = buffer p <> "\n" <> T.replicate (indent p) " "
                 })

indented =
    wrap
        (\s -> s {indent = indent s + 2})
        (\oldState newState -> newState {indent = indent oldState})

para m = indented (writeLine >> m)

softline m = fitsIfte m (para (space >> m))

space = writeNoNl " "

listParens = id

withParens f m = do
    p <- gets precedence
    when (f p) $ write "("
    r <- m
    when (f p) $ write ")"
    return r

surround lhs rhs [] = lhs >> rhs
surround lhs rhs doc =
    fitsIfte
        (lhs >> space >> interp space doc >> space >> rhs)
        (lhs >> indented (writeLine >> interp writeLine doc) >> writeLine >> rhs)

peekWrite txt = do
    s <- get
    write txt
    s1 <- get
    put s
    return s1

fitsLine m = do
    orig <- get
    r <- m
    s <- get
    if column s > pageWidth orig || line s > line orig
        then put orig >> return Nothing
        else return $ Just r

fitsIfte a b = do
    r <- fitsLine a
    case r of
        Nothing -> b
        Just b' -> return b'

interp doc x =
    forM_ (zip [0 ..] x) $ \(i, x') -> do
        when (i > 0) $ doc
        x'

main :: IO ()
main
    -- r <- parseNixFile "tests/lists.nix"
 = do
    r <- parseNixFile "/Users/judet/.nixos/darwin-configuration.nix"
    case r of
        Success r' -> T.putStrLn . buffer =<< execStateT (go r') defaultState
        Failure p -> print p

go = go' . unFix

go' (NSym vn) = write vn
go' (NList exprs) = surround (write "[") (write "]") $ map (withPrec 15 . go) exprs
go' (NConstant c) = writeConst c
go' (NAbs pset rhs) = withParens (> 10) $ hsep [writeParamSet pset, go rhs]
go' (NBinary op lhs rhs) =
    withParens (>= prec') $ do
        let lhs' = withPrec prec' $ go lhs
            rhs' = do
                when (op /= NApp) $ writeOp op >> write " "
                withPrec prec' $ go rhs
        fitsIfte (hsep [lhs', rhs']) (lhs' >> para rhs')
  where
    prec' =
        case op of
            NPlus -> 9
            NMult -> 10
            NConcat -> 11
            NApp -> 14
            NUpdate -> 7
            x -> error $ show x
    writeOp NPlus = write "+"
    writeOp NMult = write "*"
    writeOp NUpdate = write "//"
    writeOp NConcat = write "++"
    writeOp x = error $ show x
go' (NIf cond e1 e2) =
    fitsIfte
        (hsep [write "if", go cond, write "then", go e1, write "else", go e2])
        (write "if " >> go cond >>
         indented
             (do writeLine
                 write "then " >> go e1
                 writeLine
                 write "else " >> go e2))
go' (NRecSet binds) = surround (write "rec {") (write "}") $ map writeBind binds
go' (NSet binds) = surround (write "{") (write "}") $ map writeBind binds
go' (NSelect expr path def) = do
    withPrec 16 $ go expr
    write "."
    writePath path
    forM_ def $ \expr -> do
        write " or "
        go expr
go' (NLet binds rhs) =
    withParens (>= 15) $ do
        write "let"
        para $ vcat $ map writeBind binds
        write "\nin"
        space
        withPrec 0 $ go rhs
go' (NStr s) = writeStr s
go' (NLiteralPath p) = write $ T.pack p
go' (NEnvPath p) = write "<" >> write (T.pack p) >> write ">"
go' (NWith expr rhs) =
    withParens (> 0) $ do
        fitsIfte (hsep [write "with", go expr]) (write "with" >> para (go expr))
        write ";"
        para $ go rhs
go' y = liftIO $ print y

writeBind (NamedVar path expr _) =
    withPrec 0 $
    fitsIfte
        (hsep [writePath path, write "=", go expr >> write ";"])
        (do hsep [writePath path, write "="]
            para $ go expr >> write ";")
writeBind (Inherit parent attrs _) = do
    write "inherit"
    space
    forM_ parent $ \p -> do
        write "("
        go p
        write ")"
        space
    fitsIfte (hsep $ map writeKey attrs) (para $ vcat $ map writeKey attrs)
    write ";"

writePath keynames = interp (write ".") $ map writeKey $ toList keynames

writeKey (StaticKey vn) = write vn
writeKey (DynamicKey antiquote) = writeAnti writeStr antiquote

writeAnti ::
       MonadIO m
    => (a -> StateT PrinterState m ())
    -> Antiquoted a NExpr
    -> StateT PrinterState m ()
writeAnti writeLit v =
    case v of
        Plain s -> writeLit s
        Antiquoted expr -> write "${" >> go expr >> write "}"

writeStr (DoubleQuoted aqs) = do
    write "\""
    mapM_ (writeAnti write) aqs
    write "\""
writeStr (Indented i aqs) = do
    write "''"
    indented $ do
        writeLine
        mapM_
            (\(i, chunk) ->
                 writeAnti
                     (write .
                      if i == length aqs
                          then T.stripEnd
                          else id)
                     chunk)
            (zip [1 ..] aqs)
    write "\n''"

writeConst (NInt dec) = write (T.pack $ show dec)
writeConst (NBool x) =
    write
        (if x
             then "true"
             else "false")
writeConst NNull = write "null"
writeConst x = error $ show x

writeParamSet (Param vn) = write vn >> write ":"
writeParamSet (ParamSet pset variadic atpattern) = do
    let docs' =
            flip map (zip [0 ..] pset) $ \(i, (vn, def)) -> do
                write
                    (if i == 0
                         then "{"
                         else ",")
                space
                write vn
                forM_ def $ \val -> do
                    space
                    write "?"
                    space
                    go val
        docs = docs' ++ [when variadic $ write ", ..."]
    fitsIfte (hcat docs >> write " }") (vcat docs >> write "\n}")
    forM_ atpattern $ \vn -> hsep [write " @", write vn]
    write ":"
