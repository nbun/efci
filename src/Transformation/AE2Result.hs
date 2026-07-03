{-# LANGUAGE FlexibleInstances #-}

{- | Result transformation

This module provides utilities for converting internal computation results
to pretty-printed output. It handles:

* Result type definitions with different value representations
* Pretty-printing of results with proper formatting
* Decluttering of results by removing redundant bindings
* Handling of evaluated, unevaluated, and error results
-}
module Transformation.AE2Result (Result (..), pretty, declutter, withoutBindings) where

import Curry.FlatCurry.Annotated.Type hiding (CombType)
import Data.List (intercalate)
import qualified Data.Map as Map
import Effect.FlatCurry.Constructor
import Effect.FlatCurry.Function
import Effect.General.Error
import Effect.General.State
import Type

{- | Declutter computation results for presentation

Takes trace info as well as computation results and removes an empty list of bindings.
-}
declutter :: (Show a) => ([TraceInfo], Error [(Constraints, Value (Closure a))]) -> ([TraceInfo], [Result])
declutter (ti, Error s) = (ti, [RError s])
declutter (ti, EOther xs) = (ti, map addBindings xs)
  where
    addBindings (bs, v)
        | Map.null bs = declutterHNF v
        | otherwise = RBindings bs (declutterHNF v)

{- | Translate 'Value' into 'Result'

The translation keeps most information but replaces references
and functional values with 'Unevaluated'.
-}
declutterHNF :: (Show a) => Value (Closure a) -> Result
declutterHNF (NF qn args) = RCons qn (map declutterHNF args)
declutterHNF (HNF qn ptrs) = RCons qn (replicate (length ptrs) Unevaluated)
declutterHNF (Lit l) = RLit l
declutterHNF (Free i) = RFree i
declutterHNF (ValOther c) = case c of
    Closure qn ct args -> RClosure qn ct (length args)
    Lambda _ _ -> Unevaluated
    Effect.FlatCurry.Function.External _ -> Unevaluated
    Other x -> ROther (show x)

{- | Result type for pretty-printed output

Represents the various forms that computation results can take:

* 'RLit': Literal values
* 'RCons': Constructor applications
* 'Unevaluated': Results that weren't fully evaluated
* 'RClosure': Function closures
* 'RError': Errors
* 'RFree': Free variables
* 'ROther': Other values (usually not used)
* 'RBindings': Results with constraint bindings
-}
data Result
    = RLit Literal
    | RCons QName [Result]
    | Unevaluated
    | RClosure QName CombType Int
    | RError String
    | RFree Ptr
    | ROther String
    | RBindings Constraints Result
    deriving (Show, Eq)

-- | Pretty-printing class for result types
class Pretty a where
    -- | Convert a value to a human-readable string representation
    pretty :: a -> String

instance Pretty Result where
    pretty r@(RCons ("Prelude", ":") _) = prettyList r
    pretty (RCons ("Prelude", "(,)") [x, y]) =
        "(" ++ pretty x ++ ", " ++ pretty y ++ ")"
    pretty (RCons ("Prelude", "(,,)") [x, y, z]) =
        "(" ++ pretty x ++ ", " ++ pretty y ++ ", " ++ pretty z ++ ")"
    pretty (RCons qn []) = snd qn
    pretty (RCons qn vs) = parOnce $ snd qn ++ " " ++ unwords (map pretty vs)
    pretty (RLit (Intc i)) = show i
    pretty (RLit (Charc c)) = show c
    pretty (RLit (Floatc f)) = show f
    pretty (RFree (Ptr _ s)) = "f" ++ s
    pretty Unevaluated = "Unevaluated"
    pretty (RClosure qn ct argc) =
        snd qn ++ " " ++ unwords (replicate argc "_") ++ (if argc == 0 then "" else " ") ++ unwords (replicate (missingArgs ct) "?")
    pretty (RError s) = "Error: " ++ s
    pretty (RBindings cs r) =
        "{" ++ intercalate ", " (map pretty (Map.toList cs)) ++ "} " ++ pretty r
    pretty (ROther s) = s

instance Pretty (Ptr, CValue) where
    pretty (i, LitC l) = '_' : show i ++ " -> " ++ show l
    pretty (i, VarC j) = '_' : show i ++ " -> " ++ show j
    pretty (i, ConsC qn []) = '_' : show i ++ " -> " ++ snd qn
    pretty (i, ConsC qn vs) =
        '_'
            : show i
            ++ " -> "
            ++ parOnce (snd qn ++ " " ++ unwords (map show vs))

-- | Pretty-print a 'Result' list in short form
prettyList :: Result -> String
prettyList r = "[" ++ intercalate ", " (prettyList' r) ++ "]"
  where
    prettyList' (RCons ("Prelude", ":") [x, y]) = pretty x : prettyList' y
    prettyList' (RCons ("Prelude", "[]") []) = []
    prettyList' x = [show x]

-- | Add parentheses to a string unless they exist already
parOnce :: String -> String
parOnce "" = ""
parOnce s@('(' : _) = s
parOnce s = '(' : s ++ ")"

-- | Remove bindings from a result, returning the underlying value
withoutBindings :: Result -> Result
withoutBindings (RBindings _ r) = withoutBindings r
withoutBindings r = r