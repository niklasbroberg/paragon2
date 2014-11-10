{-# LANGUAGE PatternGuards #-}

module Language.Java.Paragon.XML 
  (XMLNode, xmlToNatural)
  where

import Language.Java.Paragon.Error
import Language.Java.Paragon.Interaction (versionString)

import Data.List (stripPrefix, find)
import Data.Maybe (fromMaybe)

data XMLAttribute = XMLAttribute String -- attribute name
                                 String -- attribute value

instance Show XMLAttribute where
  show (XMLAttribute name value) = name ++ "=\"" ++ value ++ "\""

data XMLNode = XMLNode String         -- tagname
                       [XMLAttribute] -- attributes
                       [XMLNode]      -- children
             | CData String           -- tagname
			         [XMLAttribute]   -- attributes
					 String           -- CData

showNode :: XMLNode -> Int -> String
showNode (XMLNode tag attr childs) indent = let
  r1 = replicate indent '\t'
  r2 = r1 ++ "<" ++ tag ++ (foldl (\x y-> x ++ " " ++ (show y)) "" attr) ++ ">"
  r3 = r2 ++ foldl (\x y -> x ++ "\n" ++ (showNode y (indent+1))) "" childs
  r4 = r3 ++ "\n" ++ r1 ++ "</" ++ tag ++ ">"
  in r4
showNode (CData tag attr _data) indent = let
  r1 = replicate indent '\t'
  r2 = r1 ++ "<" ++ tag ++ (foldl (\x y-> x ++ " " ++ (show y)) "" attr) ++ ">"
  r3 = r2 ++ _data ++ "</" ++ tag ++ ">"
  in r3


insertNode :: XMLNode -> XMLNode -> XMLNode
insertNode (CData _ _ _) _ = CData "ERROR" [] "Tried to insert node into CData node"
insertNode (XMLNode tag atts childs) n = XMLNode tag atts (childs ++ [n])

datanode :: String -> String -> XMLNode
datanode tag _data = CData tag [] _data

standardNode :: String -> [(String, String)] -> [(String, String)] -> XMLNode
standardNode string attr pairs =
  XMLNode string 
          [XMLAttribute a b |(a,b) <- attr] 
		  [datanode a b |(a,b) <- pairs]

instance Show XMLNode where
  show n = showNode n 0

instance Error XMLNode where
  baseError = XMLNode "parac" [XMLAttribute "version" versionString] []
  concatError = insertNode
  constructError = constructError'
  parseErrorToError perr = XMLNode "error" [] [datanode "parseError" (show perr)]
  noError = XMLNode "ok" [][]
  
constructError' :: String -> [(String, String)] -> XMLNode
constructError' string pairs
  | Just context <- stripPrefix "context_" string = standardNode context pairs []
  | otherwise = standardNode "error" [ ( "code" , safeLookup "-1" string errorCodes)
                                     , ( "type" , string)                           ]
									 pairs

safeLookup :: Eq a => b -> a -> [(a,b)] -> b
safeLookup x needle xs = fromMaybe x $ lookup needle xs 
		
errorCodes :: [(String,String)]
errorCodes = [ ( "constraint_pRHs_pV"										, "-1000" )
			 ]

xmlToNatural' :: [XMLNode] -> String
xmlToNatural' nodes = concat (map xmlToNatural nodes)
			 
xmlToNatural :: XMLNode -> String
xmlToNatural n@(XMLNode tag attr kids) = let
  f = safeLookup (\(_,_) -> "ERROR: ... could not convert following XML to natural text:\n" ++ (show n)) tag xmlToNaturalTable
  in f (map (\(XMLAttribute a b) -> (a,b)) attr, kids)
xmlToNatural n = "ERROR: ... could not convert following XML to natural text:\n" ++ (show n)
			 
xmlToNaturalTable :: [(String, ([(String,String)],[XMLNode]) -> String)]
xmlToNaturalTable =
  [ ("parac" ,
      (\(attr, kids) -> (xmlToNatural' kids) --"Paragon compiler version " ++
	                    --(safeLookup "unknown" "version" attr) ++ ".\n\n" ++ (xmlToNatural' kids) )
	                    -- Leaving this out for current testsuite
	                    )
    )
  ,
    ("class" ,
      (\(attr, kids) -> "In the context of the class " ++ 
	                    (safeLookup "[unknown class]" "name" attr) ++
						":\n" ++(xmlToNatural' kids) )
    )
  , ("method",
      (\(attr, kids) -> "In the context of the method body " ++ 
	                   (safeLookup "[unknown method]" "name" attr) ++ 
					   ":\n" ++ (xmlToNatural' kids) )
    )
  , ("lockstate",
      (\(attr, kids) -> "In the context of the lockstate " ++ 
	                   (safeLookup "[unknown lockstate]" "state" attr) ++ 
					   ":\n" ++ (xmlToNatural' kids) )
    )
  , ("locksignature",
  	  (\(attr, kids) -> "When checking the signature of lock " ++ 
	                   (safeLookup "[unknown lock]" "lock" attr) ++ 
					   ":\n" ++ (xmlToNatural' kids) )
    )
  , ("constructor_body",
          (\(attr, kids) -> "When checking the body of constructur " ++
	                   (safeLookup "[unknown constructor]" "name" attr) ++ 
					   ":\n" ++ (xmlToNatural' kids) )
    )
  , ("error",
      (\(attr, kids) -> naturalError (safeLookup "__undefined__" "type" attr) kids)
	)
  , ("ok", (\_ -> ""))
  ]

naturalError :: String -> [XMLNode] -> String
naturalError err nodes = let
  f = safeLookup (\_ -> "ERROR: ... could not find translation for " ++ err ++ ". XML:\n" ++ (concat $ map show nodes)) err errorToNaturalTable
  in f nodes
  
errorToNaturalTable :: [(String, ([XMLNode] -> String))]
errorToNaturalTable =
  [ ("constraint_pRHs_pV" ,
      (\nodes -> "Cannot assign the result of expression " ++
	             (cdataValue "fromExpression" nodes) ++ " with policy " ++
				 (cdataValue "fromPolicy" nodes) ++ " to location " ++
				 (cdataValue "toLocation" nodes) ++ " with policy " ++
				 (cdataValue "toPolicy" nodes) )
	)
  , ("__undefined__" ,
     (\nodes -> "Error type not specified Content in XML: \n" ++ (concat $ map show nodes))
	)
  ]


cdataValue :: String -> [XMLNode] -> String
cdataValue tag nodes = let 
  node = find findTag nodes
  in fromMaybe "[not found]" $ fmap (\n -> getVal n) node
  where 
    findTag :: XMLNode -> Bool
    findTag (CData _tag _ _) = tag == _tag
    findTag _ = False
    getVal :: XMLNode -> String
    getVal (CData _ _ val) = val
    getVal _ = "[is no CDATA element!]"
						   
  
  
{-
handleContext :: String -> [(String, String)]  -> XMLNode
handleContext string pairs
  | string == "Class"      = standardNode "class"  [("hideString","1"):pairs] []
  | string == "Methodbody" = standardNode "method" [("hideString","1"):pairs] []
  | otherwise = standardNode string [("new",0)] ( [datanode a b |(a,b) <- pairs] ++ [datanode "string" expl] )
-}
													 
--sample = XMLNode "hello" [XMLAttribute "attr1" "value1", XMLAttribute "attr2" "value2"] 
--            [ XMLNode "baby1" [XMLAttribute "attr1" "value1", XMLAttribute "attr2" "value2"] [],
--              XMLNode "baby2" [] [CData "Blablabal"] ]
