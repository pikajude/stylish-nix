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

data Foo a b = a :+ b deriving Show

infixl 7 :+

{-
== Nix precedence table

* taken from https://gist.github.com/joepie91/c3c047f3406aea9ec65eebce2ffd449d
  but reversed for ergonomics
* "inside list" precedence added. this is one higher than function application

15 SELECT e.attrpath [or default value]
14 INLIST [ a b c ]
13 APP f arg1 arg2
12 NEG -e
11 HAS_ATTR e ? attrpath
10 CONCAT e1 ++ e2
9 MUL, DIV e1 * e2, e1 / e2
8 ADD, SUB e1 + e2, e1 - e2
7 NOT !e
6 UPDATE e1 // e2
5 LT, LTE, GT, GTE
4 EQ, NEQ
3 AND &&
2 OR ||
1 IMPL e1 -> e2

-}
data PrinterState = PrinterState
    { pageWidth :: Int
    , column :: Int
    , line :: Int
    , indent :: Int
    , buffer :: Text
    , precedence :: Int
    } deriving (Show)

defaultState = PrinterState 12 0 0 0 "" 0

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
main = do
    r <- parseNixFile "tests/lists.nix"
    case r of
        Success r' -> T.putStrLn . buffer =<< execStateT (go r') defaultState
        Failure p -> print p

go = go' . unFix

go' (NSym vn) = write vn
go' (NList exprs) = surround (write "[") (write "]") $ map (withPrec 14 . go) exprs
go' (NConstant c) = writeConst c
go' (NAbs pset rhs) = withParens (> 10) $ hsep [write "{}:", go rhs]
go' (NBinary op lhs rhs) =
    withParens (> prec') $ do
        withPrec prec' $ go lhs
        write " "
        when (op /= NApp) $ writeOp op >> write " "
        withPrec prec' $ go rhs
  where
    prec' =
        case op of
            NPlus -> 8
            NMult -> 9
            NApp -> 13
            NUpdate -> 6
            x -> error $ show x
    writeOp NPlus = write "+"
    writeOp NMult = write "*"
    writeOp NUpdate = write "//"
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
    go expr
    write "."
    writePath path
    forM_ def $ \expr -> do
        write " or "
        go expr
go' y = liftIO $ print y

writeBind (NamedVar path expr _) =
    fitsIfte
        (hsep [writePath path, write "=", go expr >> write ";"])
        (do hsep [writePath path, write "="]
            para $ go expr >> write ";")

writePath keynames = interp (write ".") $ map writeKey $ toList keynames

writeKey (StaticKey vn) = write vn

writeConst (NInt dec) = write (T.pack $ show dec)
writeConst (NBool x) =
    write
        (if x
             then "true"
             else "false")
writeConst NNull = write "null"
writeConst x = error $ show x
