module Interpreter where

import AbsCPP
import PrintCPP
import ErrM

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe


data Env =  Env (Sig,[Context]) -- functions are context stack 
type Sig = Map Id Def -- function type signature
type Context = Map Id Val --- variables wih their Value


data Val
  = VInt Integer
  | VDouble Double
  | VBool Bool
  | VVoid
  | VUndefined

prettyVal :: Val -> String
prettyVal v = case v of
  VInt i      -> show i
  VDouble d   -> show d
  VBool True  -> "true"
  VBool False -> "false"
  VVoid       -> "void"
  VUndefined  -> "undefined"

interpret :: Program -> IO ()
interpret (PDefs defs) = do
  -- Build initial environment with all function definitions.
  let env = foldl updateFun emptyEnv defs
  let (DFun  _t _i _args ss) = lookupFun env (Id "main")
  foldM_ inthelp env ss

inthelp :: Env -> Stm -> IO (Env)
inthelp en st = do 
        (v,env0) <- (exec en st) 
        return env0

exechelp :: (Val,Env) -> Stm -> IO (Val,Env)
exechelp (a,env) st = case a of 
  VUndefined -> do 
    (v,env0) <- (exec env st)
    return (v,env0)
  otherwise -> do 
    (v,env0) <- (exec env st)
    return (a,env0)

exec :: Env -> Stm -> IO (Val,Env)
exec env s = case s of
  SInit t x e -> do
    (v, env') <- eval env e
    return (VUndefined ,(updateVar env' v x))

  SExp e -> do
    (v, env') <- eval env e
    return (VUndefined,env')

  SDecls t is -> do
    return $ (VUndefined ,(foldl (\ x y -> updateVar x VUndefined y) env is))

  SWhile e s -> do
    (v, env2) <- eval env e
    if ((\ (VBool x) -> x) v)
      then 
        do
          (v,env3) <- (exec env2 s)
          exec env3 (SWhile e s)
      else 
        return (VUndefined,env2)

  SBlock ss -> do
    let env2 = newBlock env
    foldM (exechelp) (VUndefined,env2) ss
     

    --return (exitBlock env3)

  SIfElse e s1 s2 -> do 
    (v, env2) <- eval env e
    if ((\ (VBool x) -> x) v)
      then 
        exec env2 s1
      else
        exec env2 s2

  SReturn e -> do 
       eval env e
      



  _ -> do
    putStrLn $ "NYI: exec " ++ printTree s
    return (VUndefined ,env)

eval :: Env -> Exp -> IO (Val, Env)
eval env e = case e of
  EInt i -> return (VInt i, env)
  EDouble d -> return (VDouble d, env)
  EId x  -> return (lookupVar env x, env)
  ETrue -> return (VBool True,  env)
  EFalse -> return (VBool False, env)

  EApp f es -> do
    (vs, env') <- loop env es
    v <- invoke env' f vs
    return (v, env')
    where
      loop env [] = return ([], env)
      loop env (e : es) = do
        (v , env' ) <- eval env e
        (vs, env'') <- loop env' es
        return (v : vs, env'')

  EPostIncr e -> case e of 
    (EId x) -> do
                (v, env') <- eval env e
                let env'' = setVar env' (incr v) x
                return (v, env'')
    otherwise -> do 
                eval env e
                 

  EPostDecr e -> case e of
    (EId x) -> do
                (v, env') <- eval env e
                let env'' = setVar env' (decr v) x
                return (v, env'')
    otherwise -> do 
                eval env e

  EPreIncr e -> case e of
    (EId x) -> do
                (v, env') <- eval env e
                let env'' = setVar env' (incr v) x
                return ((incr v), env'')
    otherwise -> do 
                eval env e

  EPreDecr e -> case e of
    (EId x) -> do
                (v, env') <- eval env e
                let env'' = setVar env' (decr v) x
                return ((decr v), env'')
    otherwise -> do 
                eval env e

  ETimes e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((mul v1 v2), env2)

  EDiv e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((division v1 v2), env2)

  EPlus e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((add v1 v2) , env2)

  EMinus e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2 
    return ((sub v1 v2), env2)

  ELt e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((lowerThan v1 v2), env2)

  EGt e1 e2 -> do 
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((greaterThan v1 v2), env2)

  ELtEq e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((lowerThanEqual v1 v2), env2)

  EGtEq e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((greaterThanEqual v1 v2), env2)

  EEq e1 e2 -> do
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((equal v1 v2) , env2)

  ENEq e1 e2 -> do 
    (v1, env1) <- eval env e1
    (v2, env2) <- eval env1 e2
    return ((notequal v1 v2), env2)

  EAnd e1 e2 -> do 
    (v1, env1) <- eval env e1
    if ((\(VBool x) -> x) v1 )
      then 
        do
        (v2, env2) <- eval env1 e2
        return ((conjunction v1 v2), env2)
      else
        return ((VBool False),env1)
    

  EOr e1 e2 -> do 
    (v1, env1) <- eval env e1
    if ((\(VBool x) -> x) v1 )
      then
          return (v1,env1)
      else
        do        
          (v2, env2) <- eval env1 e2
          return ((disjunction v1 v2), env2)

  EAss (EId x) e2 -> do
                (v1, env1) <- eval env e2
                let env2 = setVar env1 (v1) x 
                return (v1, env2)


  _ -> do
    putStrLn $ "NYI: eval " ++ printTree e
    return (VVoid, env)

invoke :: Env -> Id -> [Val] -> IO Val
invoke env f vs = case f of
  Id "printInt" -> do
    mapM_ (putStrLn . prettyVal) vs
    return VVoid
  Id "printDouble" -> do
    mapM_ (putStrLn . prettyVal) vs
    return VVoid
  Id "readInt" -> do
    vs <- getLine
    let x = read vs :: Integer
    return (VInt x)

  Id "readDouble" -> do
    vs <- getLine
    let x = read vs :: Double
    return (VDouble x)

  _ -> do
--    let (args,_t) = lookupFun env fr
    let DFun _t _f args ss = lookupFun env f
    let xvs = zip (map (\ (ADecl _t x) -> x) args) vs -- [(Id,Val)]
    let env' = foldl (\ env (x,v)  -> updateVar env v x) (newBlock env) xvs
    (invokehelp ss env')



invokehelp :: [Stm] -> Env -> IO Val 
invokehelp [] env = do return VVoid  
invokehelp (s:ss) env =  
  do
    bol <- (exec env s)
    case bol of 
      (VUndefined,env1) -> invokehelp ss env1 
      (a,env1) -> return a






lookupFun :: Env -> Id -> Def 
lookupFun (Env (sig,context)) f = Map.findWithDefault err f sig
  where err = error $ "undefined function " ++ printTree f


lookupVar :: Env -> Id -> Val
lookupVar (Env (sig,context)) x = case catMaybes $ map (Map.lookup x) context of
  []      -> error $ "unbound variable "  ++ printTree x
  (v : _) ->  v

updateFun :: Env -> Def -> Env
updateFun (Env (sig,context)) def@(DFun ty i args ss) = do (Env ((Map.insert i def sig), context))
  where targs = (map (\ (ADecl t _x) -> t) args)

updateVar :: Env -> Val -> Id -> Env
updateVar (Env (sig,(c:con))) v i = Env (sig,((Map.insert i v c):con))

setVar :: Env -> Val -> Id -> Env
setVar (Env (sig,(c:con))) v i = case (c:con) of
  [] -> error $ "unbound variable " ++ printTree i
  (x:xs) -> case Map.member i x of
    True -> (Env (sig, (Map.insert i v x : (c:con))))
    False -> setVar (Env (sig,(con))) v i

newBlock :: Env -> Env 
newBlock (Env (sig,context)) = Env (sig, Map.empty : context)
 --newBlock env = env { envCxt = Map.empty : envCxt env }

exitBlock :: Env -> Env
exitBlock (Env (sig,(c:con))) = (Env (sig,(con)))

emptyEnv :: Env
emptyEnv = Env (Map.empty,[Map.empty])



------ Mathematical Operands

incr :: Val -> Val
incr v = case v of
  VInt i -> VInt $ i + 1
  VDouble d -> VDouble $ d + 1
  v -> error $ "cannot increment value " ++ prettyVal v

decr :: Val -> Val
decr v = case v of
  VInt i -> VInt $ i - 1
  VDouble d -> VDouble $ d - 1
  v -> error $ "cannot increment value " ++ prettyVal v

mul :: Val -> Val -> Val
mul (VInt v1) (VInt v2) = VInt (v1*v2)
mul (VDouble v1) (VDouble v2) = VDouble (v1*v2)

division :: Val -> Val -> Val
division (VInt v1) (VInt v2) = VInt (v1 `div` v2)
division (VDouble v1) (VDouble v2) = VDouble (v1 / v2)

add :: Val -> Val -> Val
add (VInt v1) (VInt v2) = VInt (v1+v2)
add (VDouble v1) (VDouble v2) = VDouble (v1+v2)

sub :: Val -> Val -> Val
sub (VInt v1) (VInt v2) = VInt (v1-v2)
sub (VDouble v1) (VDouble v2) = VDouble (v1-v2)

lowerThan :: Val -> Val -> Val
lowerThan (VInt v1) (VInt v2) = VBool (v1<v2)
lowerThan (VDouble v1) (VDouble v2) = VBool (v1<v2)

greaterThan :: Val -> Val -> Val
greaterThan (VInt v1) (VInt v2) = VBool (v1>v2)
greaterThan (VDouble v1) (VDouble v2) = VBool (v1>v2)

lowerThanEqual :: Val -> Val -> Val
lowerThanEqual (VInt v1) (VInt v2) = VBool (v1 <= v2)
lowerThanEqual (VDouble v1) (VDouble v2) = VBool (v1 <= v2)

greaterThanEqual :: Val -> Val -> Val
greaterThanEqual (VInt v1) (VInt v2) = VBool (v1 >= v2)
greaterThanEqual (VDouble v1) (VDouble v2) = VBool (v1 >= v2)

equal :: Val -> Val -> Val
equal (VInt v1) (VInt v2) = VBool (v1 == v2)
equal (VDouble v1) (VDouble v2) = VBool (v1 == v2)
equal (VBool v1) (VBool v2) = VBool (v1 == v2)

notequal :: Val -> Val -> Val
notequal (VInt v1) (VInt v2) = VBool (v1 /= v2)
notequal (VDouble v1) (VDouble v2) = VBool (v1 /= v2)
notequal (VBool v1) (VBool v2) = VBool (v1 /= v2)

conjunction :: Val -> Val -> Val
conjunction (VBool v1) (VBool v2) = VBool (v1 && v2)

disjunction :: Val -> Val -> Val
disjunction (VBool v1) (VBool v2) = VBool (v1 || v2)



