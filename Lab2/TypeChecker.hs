module TypeChecker where
-- (PDefs [(DFun Type_bool (Id "Main") [] [(SReturn (EInt 1))] ),(DFun Type_int (Id "iain") [] [(SReturn ETrue)] ),(DFun Type_int (Id "nain") [] [(SReturn ETrue)] )] )

-- [(SExp ETrue) ,(SReturn ETrue),(SWhile ETrue (SReturn ETrue)),(SBlock [(SReturn ETrue),(SReturn ETrue)]),(SIfElse ETrue (SReturn ETrue) (SReturn ETrue))]
-- Haskell module generated by the BNF converter
import AbsCPP
import PrintCPP
import ErrM

import Control.Monad

import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

data Env =  Env (Sig,[Context]) -- functions are context stack 
type Sig = Map Id ([Type],Type) -- function type signature
type Context = Map Id Type --- variables wih their type

std_functions = [((Id "readDouble"),([],Type_double)),((Id "readInt"),([],Type_int)),((Id "printDouble"),([Type_double],Type_void)),((Id "printInt"),([Type_int],Type_void))]

-- + Functions needed + 
-- inferExp   : infer type of Exp
-- checkExp   : check type of Exp
-- ?          : check sequence of stms
-- checkDef   : check funcktion definition
-- typecheck  : check whole progarm
-- lookupVar  : look up variable 
-- lookupFun  : look up function
-- updateVar  : extend env with variable
-- updateFun  : extend env with function
-- newBlock   : enter new block 
-- emptyEnv   : empty environment   


-- 1. Define the appropriate auxiliary fuctions and types
-- 2. Implement typechecker and inference functions
inferExp :: Env -> Exp -> Err Type
inferExp env x = case x of
  ETrue -> return Type_bool
  EFalse -> return Type_bool
  EDouble d -> return Type_double
  EInt n -> return Type_int

  EId i -> do 
    typ <- lookupVar env i
    return typ

  EApp i es -> do 
    (func,ft) <- lookupFun env i
    if (length es /= length func) 
      then 
        fail $ "incorrect number of arguments to function " ++ printTree i
      else
        --ft <$ zipWithM_ (checkExp env) es func
        return ft
    
  EPostIncr e -> do
    t <- inferExp env e
    unless (t `elem` [Type_int, Type_double]) $ fail $
      "expected numberic type, but found " ++ printTree t ++
      " when checking " ++ printTree e
    return t

  EPostDecr e -> do
    t <- inferExp env e
    unless (t `elem` [Type_int, Type_double]) $ fail $
      "expected numberic type, but found " ++ printTree t ++
      " when checking " ++ printTree e
    return t


  EPreIncr e -> do
    t <- inferExp env e
    unless (t `elem` [Type_int, Type_double]) $ fail $
      "expected numberic type, but found " ++ printTree t ++
      " when checking " ++ printTree e
    return t

  EPreDecr e -> do
    t <- inferExp env e
    unless (t `elem` [Type_int, Type_double]) $ fail $
      "expected numberic type, but found " ++ printTree t ++
      " when checking " ++ printTree e
    return t

 -- ETimes Exp Exp
  ETimes e1 e2 -> do
    inferBin [Type_int, Type_double] env e1 e2
 -- EDiv Exp Exp
  EDiv e1 e2 -> do
    inferBin [Type_int, Type_double] env e1 e2
 -- EPlus Exp Exp
  EPlus e1 e2 -> do
    inferBin [Type_int, Type_double] env e1 e2
 -- EMinus Exp Exp
  EMinus e1 e2 -> do
    inferBin [Type_int, Type_double] env e1 e2
 -- ELt Exp Exp
  ELt e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if a `elem` [Type_int, Type_double]
      then
        return Type_bool
      else
        return a
 -- EGt Exp Exp
  EGt e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if a `elem` [Type_int, Type_double]
      then
        return Type_bool
      else
        return a
 -- ELtEq Exp Exp
  ELtEq e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if a `elem` [Type_int, Type_double]
      then
        return Type_bool
      else
        return a
 -- EGtWq Exp Exp
  EGtEq e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if a `elem` [Type_int, Type_double]
      then
        return Type_bool
      else
        return a
 -- EEq Exp Exp
  EEq e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if a `elem` [Type_int, Type_double]
      then
        return Type_bool
      else
        return a

 -- ENEq Exp Exp
  ENEq e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if elem a [Type_int, Type_double]
      then
        return Type_bool
      else
        return a
 -- EAnd Exp Exp
  EAnd e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if elem a [Type_int, Type_double]
      then
        return Type_bool
      else
        return a
 -- EOr Exp Exp
  EOr e1 e2 -> do
    a <- inferBin [Type_int, Type_double, Type_bool] env e1 e2 
    if elem a [Type_int, Type_double]
      then
        return Type_bool
      else
        return a

 -- EAss Exp Exp Right Assoc?
  EAss e1 e2 -> do
    inferBin [Type_int, Type_double, Type_bool] env e1 e2

  -- otherwise -> fail $ "NYI Expression: " ++ printTree x

-- Pseudo code
-- inferExp c x = 
--     do t <- lookup(x,c)
--             return t


inferBin :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBin types env exp1 exp2 = do
  typ <- inferExp env exp1
  if (typ `elem` types)
    then do
      checkExp env typ exp2
      return typ
    else 
      fail $ "Wrong type of expression " ++ printTree exp1 

--looking up the variable is not a recursive call to check or infer, it is
-- a call to lookup that comes out as pattern maching

typecheck :: Program -> Err ()
typecheck (PDefs defs) = do
  let env0 = Env ((Map.fromList std_functions), [])  -- [] might not be a good idea
  env <- foldM updateFun env0 defs
  mapM_ (checkDef env) defs
  --fail $ (Map.showTree (con !! 0))

checkDef :: Env -> Def -> Err ()
checkDef env d@(DFun t f args ss) = do
  let env'' = newBlock env
  env' <- foldM (\ env'' (ADecl t x) -> (updateVar env'' t x)) (env'') args
  --checkStms env' ss
  env3 <- foldM checkStm env' ss
  --let env'' = newBlock env
  --Env (sig',context') <- (helpfunction env' (map (\(ADecl t x)-> t ) args) (map (\(ADecl t x)-> x) args))
  mapM_ (checkExp env3 t) (findReturn ss) 
  
  

findReturn :: [Stm] -> [Exp]
findReturn [] = []
findReturn (s:ss) = case s of 
  (SReturn a) -> (a : (findReturn ss))
  (SBlock (a:as)) -> ((findReturn [a] ) ++ (findReturn as))
  (SIfElse _ s1 s2) -> ((findReturn [s1] ) ++ (findReturn [s2] ))
  otherwise -> (findReturn ss)



checkStms :: Env -> [Stm] -> Err ()
checkStms env ss = foldM_ checkStm env ss

checkStm :: Env -> Stm -> Err Env
checkStm env@(Env (sig, (c:con))) s = case s of
  SInit t x e -> do
    checkExp env t e
    updateVar env t x
  SExp e -> do 
    t' <- inferExp env e
    checkExp env t' e 
    return env
--  SReturn e -> do
--    t' <- inferExp env e
    --checkExp env t' e 
--    return env

  SReturn e -> do
    --fail $ Map.showTree c ++ " - "
    t' <- inferExp env e
    --fail $ Map.showTree c ++ " - " ++ printTree t'
    return env
  --env <$ inferExp env e
  SWhile e s -> do 
    t' <- inferExp env e
    if (t' == Type_bool) 
      then
        do 
        a <- checkStm env s
        return env
      else
        fail $ "While: " ++ printTree e ++ " Has type " ++ printTree t'  
        
  SBlock ss -> do 
    let env1 = newBlock env
    --checkStms env1 ss
    --return env1
    checkStms env1 ss
    return env
  
  SIfElse e s1 s2 -> do
    t' <- inferExp env e
    if (t' == Type_bool) 
      then
        do  
        a <- checkStm env s1
        b <- checkStm env s2
        return env
      else
        fail $ "IF Else: " ++ printTree e ++ " Has type " ++ printTree t' 
  SDecls t xs -> do
    env1 <- helpfunction env (take (length xs) (repeat t))  xs
    return env1 
  --_ -> fail $ "NYI: checkStm "  ++ printTree s

helpfunction :: Env -> [Type] -> [Id] -> Err Env  
helpfunction  env t [] = return env
helpfunction  env (t:ts) (i:is) = do 
  env1 <- updateVar env t i
  helpfunction env1 ts is

checkExp :: Env -> Type -> Exp -> Err () 
checkExp env typ expr  = do 
  t' <- inferExp env expr 
  if (typ == t')
    then 
      return ()
    else
      fail $ "Type of: " ++ printTree expr ++ 
      " expected "++ printTree typ ++ 
      " but found " ++ printTree t'

--  + Auxiliary operations on the environment
lookupVar :: Env -> Id -> Err Type
lookupVar (Env (sig,context)) x = case catMaybes $ map (Map.lookup x) context of
  []      -> fail $ "unbound variable " ++ printTree x
  (t : _) -> return t

lookupFun :: Env -> Id -> Err ([Type],Type) 
lookupFun (Env (sig,context)) f = case Map.lookup f sig of
  Nothing -> fail $ "undefined function " ++ printTree f
  Just t  -> return t

updateVar :: Env -> Type -> Id -> Err Env
updateVar (Env (sig,(c:con))) t i = do
  if (Map.member i c)
    then
      fail $ "duplicate variable " ++ printTree i ++ " found"
    else
      return (Env (sig,((Map.insert i t c):con)))
--updateVar b t i = fail $ ("-> "++ (printTree t) ++" "++ (printTree i))

--extendCxt env@Env{ envCxt = b : bs } x t = env { envCxt = Map.insert x t b : bs }

updateFun :: Env -> Def -> Err Env
updateFun d@(Env (sig,context)) (DFun ty i args ss) = do
  if Map.member i sig  
    then
      fail $ "duplicate function "  ++ printTree i ++ " found" 
    else
      do
      return (Env ((Map.insert i (is,ty) sig), context)) where is = (map (\ (ADecl t _x) -> t) args)

newBlock :: Env -> Env 
newBlock (Env (sig,context)) = Env (sig, Map.empty : context)
--newBlock env = env { envCxt = Map.empty : envCxt env }

emptyEnv :: Env
emptyEnv = Env (Map.empty,[Map.empty])

--[c1,c2,c3. osv] -> true `elem` [true,true]

--------------------------
--1,10,104,105
--------------------------
-- 1. first environment -> emptyEnv
-- 2. newBlocks for all defs




