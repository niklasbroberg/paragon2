{-# LANGUAGE CPP, DeriveDataTypeable, DeriveFunctor, TemplateHaskell,
             FlexibleContexts, MultiParamTypeClasses, FlexibleInstances #-}
module Language.Java.Paragon.Syntax (
    module Language.Java.Paragon.Syntax,
    module Language.Java.Paragon.Annotated
                                    ) where

import Data.Data

import Language.Java.Paragon.Annotated
import Language.Java.Paragon.Interaction
import Language.Java.Paragon.SourcePos

import qualified Data.ByteString.Char8 as B

syntaxModule :: String
syntaxModule = libraryBase ++ ".Syntax"

-----------------------------------------------------------------------
-- Packages


-- | A compilation unit is the top level syntactic goal symbol of a Java program
-- This usually corresponds to a single .java source file that may start with
-- a package declaration, followed by a (possibly empty) list of imports and
-- a (usually non-empty) list of type declaration, where a type is a class
-- or interface.
-- Note that the paragon compiler currently only accepts a single type per
-- compilation unit and does not yet suport enums, although files containing
-- enums can be parsed
data CompilationUnit a = CompilationUnit a (Maybe (PackageDecl a)) [ImportDecl a] [TypeDecl a]
#ifdef __GLASGOW_HASKELL__
  deriving (Eq,Ord,Show,Typeable,Data,Functor)
#else
  deriving (Eq,Ord,Show)
#endif

-- | A package declaration appears within a compilation unit to indicate the package to which the compilation unit belongs.
data PackageDecl a = PackageDecl a (Name a)
#ifdef __GLASGOW_HASKELL__
  deriving (Eq,Ord,Show,Typeable,Data,Functor)
#else
  deriving (Eq,Ord,Show)
#endif

-- | An import declaration allows a static member or a named type to be referred
-- to by a single unqualified identifier.
-- The first argument signals whether the declaration only imports static
-- members.
-- The last argument signals whether the declaration brings all names in the
-- named type or package, or only brings a single name into scope.
data ImportDecl a
    = SingleTypeImport     a (Name a)
      -- ^Import a single type (class/interface/enum)
    | TypeImportOnDemand   a (Name a)
      -- ^Bring all types of package into scope, e.g. import java.lang.util.*
    | SingleStaticImport   a (Name a) (Ident a)
      -- ^Single static import, e.g. import static java.lang.Math.PI
    | StaticImportOnDemand a (Name a)
      -- ^Static import of all members, e.g. import static java.lang.Math.*
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-----------------------------------------------------------------------
-- Declarations

-- | A type declaration declares a class type or an interface type.
data TypeDecl a
    = ClassTypeDecl a (ClassDecl a)
    | InterfaceTypeDecl a (InterfaceDecl a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A class declaration specifies a new named reference type.
-- Note that the compiler does not actually deal with enums yet!
data ClassDecl a
    = ClassDecl a [Modifier a] (Ident a) [TypeParam a] (Maybe (ClassType a)) [ClassType a] (ClassBody a)
      -- ^Fields: Class modifiers, class identifier, type params, super class,
      -- if any, list of implemented interfaces, class body
    | EnumDecl  a [Modifier a] (Ident a)                                     [ClassType a] (EnumBody a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A class body may contain declarations of members of the class, that is,
--   fields, classes, interfaces and methods.
--   A class body may also contain instance initializers, static
--   initializers, and declarations of constructors for the class.
data ClassBody a = ClassBody a [Decl a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | The body of an enum type may contain enum constants.
data EnumBody a = EnumBody a [EnumConstant a] [Decl a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | An enum constant defines an instance of the enum type.
data EnumConstant a = EnumConstant a (Ident a) [Argument a] (Maybe (ClassBody a))
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | An interface declaration introduces a new reference type whose members
--   are classes, interfaces, constants and abstract methods. This type has
--   no implementation, but otherwise unrelated classes can implement it by
--   providing implementations for its abstract methods.
data InterfaceDecl a
    = InterfaceDecl a [Modifier a] (Ident a) [TypeParam a] [ClassType a] (InterfaceBody a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | The body of an interface may declare members of the interface.
data InterfaceBody a
    = InterfaceBody a [MemberDecl a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A declaration is either a member declaration, or a declaration of an
--   initializer, which may be static.
data Decl a
    = MemberDecl a (MemberDecl a)
    | InitDecl a Bool (Block a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-- | A class or interface member can be an inner class or interface, a field or
--   constant, or a method or constructor. An interface may only have as members
--   constants (not fields), abstract methods, and no constructors.
data MemberDecl a
    -- | The variables of a class type are introduced by field declarations.
    = FieldDecl a [Modifier a] (Type a) [VarDecl a]
    -- | A method declares executable code that can be invoked, passing a fixed number of values as arguments.
    | MethodDecl a      [Modifier a] [TypeParam a] (ReturnType a) (Ident a) [FormalParam a] [ExceptionSpec a] (MethodBody a)
    -- | A constructor is used in the creation of an object that is an instance of a class.
    | ConstructorDecl a [Modifier a] [TypeParam a]                  (Ident a) [FormalParam a] [ExceptionSpec a] (ConstructorBody a)
    -- | A member class is a class whose declaration is directly enclosed in another class or interface declaration.
    | MemberClassDecl a (ClassDecl a)
    -- | A member interface is an interface whose declaration is directly enclosed in another class or interface declaration.
    | MemberInterfaceDecl a (InterfaceDecl a)

-- Paragon
    -- | A lock declaration is a special kind of field declaration.
    | LockDecl a   [Modifier a]  (Ident a) [RefType a] (Maybe (LockProperties a))
{-    -- | A policy declaration - should be a field decl really.
    | PolicyDecl a [Modifier a] Ident Policy -}
{-    -- | An actor declaration is a special kind of field declaration.
    | ActorDecl [Modifier] Ident (Maybe VarInit) -}
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- int x; => VarDecl (VarId "x") Nothing
-- int x = 1; => VarDecl (VarId "x") (Just ...)
-- | A declaration of a variable, which may be explicitly initialized.
data VarDecl a
    = VarDecl a (VarDeclId a) (Maybe (VarInit a))
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | The name of a variable in a declaration, which may be an array.
data VarDeclId a
    = VarId a (Ident a)
    | VarDeclArray a (VarDeclId a)
    -- ^ Multi-dimensional arrays are represented by nested applications of 'VarDeclArray' (Deprecated)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

getVarDeclId :: VarDeclId a -> Ident a
getVarDeclId (VarId _ ident) = ident
getVarDeclId (VarDeclArray _ varDeclId) = getVarDeclId varDeclId

-- | Explicit initializer for a variable declaration.
data VarInit a
    = InitExp a (Exp a)
    | InitArray a (ArrayInit a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A formal parameter in method declaration. The last parameter
--   for a given declaration may be marked as variable arity,
--   indicated by the boolean argument.
data FormalParam a = FormalParam a [Modifier a] (Type a) Bool (VarDeclId a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

getFormalParamId :: FormalParam a -> Ident a
getFormalParamId (FormalParam _ _ _ _ varDeclId) = getVarDeclId varDeclId

-- | A method body is either a block of code that implements the method or simply a
--   semicolon, indicating the lack of an implementation (modelled by 'Nothing').
data MethodBody a = MethodBody a (Maybe (Block a))
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | The first statement of a constructor body may be an explicit invocation of
--   another constructor of the same class or of the direct superclass.
data ConstructorBody a = ConstructorBody a (Maybe (ExplConstrInv a)) [BlockStmt a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | An explicit constructor invocation invokes another constructor of the
--   same class, or a constructor of the direct superclass, which may
--   be qualified to explicitly specify the newly created object's immediately
--   enclosing instance.
data ExplConstrInv a
    = ThisInvoke         a         [NonWildTypeArgument a] [Argument a]
    | SuperInvoke        a         [NonWildTypeArgument a] [Argument a]
    | PrimarySuperInvoke a (Exp a) [NonWildTypeArgument a] [Argument a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-- | A modifier specifying properties of a given declaration. In general only
--   a few of these modifiers are allowed for each declaration type, for instance
--   a member type declaration may only specify one of public, private or protected.
data Modifier a
    = Public    a
    | Private   a
    | Protected a
    | Abstract  a
    | Final     a
    | Static    a
    | StrictFP  a
    | Transient a
    | Volatile  a
    | Native    a

    | Typemethod a
    | Reflexive  a
    | Transitive a
    | Symmetric  a
    | Readonly   a
    | Notnull    a

    | Reads   a (Policy a)
    | Writes  a (Policy a)
    | Opens   a [Lock a]
    | Closes  a [Lock a]
    | Expects a [Lock a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

isMethodStatic :: [Modifier a] -> Bool
isMethodStatic ms = Static () `elem` removeAnnotationMany ms

-----------------------------------------------------------------------
-- Statements

-- | A block is a sequence of statements, local class declarations
--   and local variable declaration statements within braces.
data Block a = Block a [BlockStmt a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)



-- | A block statement is either a normal statement, a local
--   class declaration or a local variable declaration.
data BlockStmt a
    = BlockStmt a (Stmt a)
    | LocalClass a (ClassDecl a)
    | LocalVars a [Modifier a] (Type a) [VarDecl a]

-- Paragon
    | LocalLock a [Modifier a] (Ident a) [RefType a] (Maybe (LockProperties a))
{-    | LocalPolicy [Modifier] Ident Policy
      | LocalActor [Modifier] Ident (Maybe VarInit) -}
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-- | A Java statement.
data Stmt a
    -- | A statement can be a nested block.
    = StmtBlock a (Block a)
    -- | The @if-then@ statement allows conditional execution of a statement.
    | IfThen a (Exp a) (Stmt a)
    -- | The @if-then-else@ statement allows conditional choice of two statements, executing one or the other but not both.
    | IfThenElse a (Exp a) (Stmt a) (Stmt a)
    -- | The @while@ statement executes an expression and a statement repeatedly until the value of the expression is false.
    | While a (Exp a) (Stmt a)
    -- | The basic @for@ statement executes some initialization code, then executes an expression, a statement, and some
    --   update code repeatedly until the value of the expression is false.
    | BasicFor a (Maybe (ForInit a)) (Maybe (Exp a)) (Maybe [Exp a]) (Stmt a)
    -- | The enhanced @for@ statement iterates over an array or a value of a class that implements the @iterator@ interface.
    | EnhancedFor a [Modifier a] (Type a) (Ident a) (Exp a) (Stmt a)
    -- | An empty statement does nothing.
    | Empty a
    -- | Certain kinds of expressions may be used as statements by following them with semicolons:
    --   assignments, pre- or post-inc- or decrementation, method invocation or class instance
    --   creation expressions.
    | ExpStmt a (Exp a)
    -- | An assertion is a statement containing a boolean expression, where an error is reported if the expression
    --   evaluates to false.
    | Assert a (Exp a) (Maybe (Exp a))
    -- | The switch statement transfers control to one of several statements depending on the value of an expression.
    | Switch a (Exp a) [SwitchBlock a]
    -- | The @do@ statement executes a statement and an expression repeatedly until the value of the expression is false.
    | Do a (Stmt a) (Exp a)
    -- | A @break@ statement transfers control out of an enclosing statement.
    | Break a (Maybe (Ident a))
    -- | A @continue@ statement may occur only in a while, do, or for statement. Control passes to the loop-continuation
    --   point of that statement.
    | Continue a (Maybe (Ident a))
    -- A @return@ statement returns control to the invoker of a method or constructor.
    | Return a (Maybe (Exp a))
    -- | A @synchronized@ statement acquires a mutual-exclusion lock on behalf of the executing thread, executes a block,
    --   then releases the lock. While the executing thread owns the lock, no other thread may acquire the lock.
    | Synchronized a (Exp a) (Block a)
    -- | A @throw@ statement causes an exception to be thrown.
    | Throw a (Exp a)
    -- | A try statement executes a block. If a value is thrown and the try statement has one or more catch clauses that
    --   can catch it, then control will be transferred to the first such catch clause. If the try statement has a finally
    --   clause, then another block of code is executed, no matter whether the try block completes normally or abruptly,
    --   and no matter whether a catch clause is first given control.
    | Try a (Block a) [Catch a] (Maybe {- finally -} (Block a))
    -- | Statements may have label prefixes.
    | Labeled a (Ident a) (Stmt a)

-- Paragon
    -- | Locks can be opened or closed.
    | Open  a (Lock a)
    | Close a (Lock a)
    | OpenBlock  a (Lock a) (Block a)
    | CloseBlock a (Lock a) (Block a)
{-    -- A @when@ statement is a variant of @if@ that only tests whether locks are open.
    | WhenThen     Lock Stmt
    | WhenThenElse Lock Stmt Stmt    -}
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | If a value is thrown and the try statement has one or more catch clauses that can catch it, then control will be
--   transferred to the first such catch clause.
data Catch a = Catch a (FormalParam a) (Block a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A block of code labelled with a @case@ or @default@ within a @switch@ statement.
data SwitchBlock a
    = SwitchBlock a (SwitchLabel a) [BlockStmt a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A label within a @switch@ statement.
data SwitchLabel a
    -- | The expression contained in the @case@ must be a 'Lit' or an @enum@ constant.
    = SwitchCase a (Exp a)
    | Default a
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | Initialization code for a basic @for@ statement.
data ForInit a
    = ForLocalVars a [Modifier a] (Type a) [VarDecl a]
    | ForInitExps a [Exp a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | An exception type has to be a class type or a type variable.
type ExceptionType a = RefType a -- restricted to ClassType or TypeVariable

data ExceptionSpec a = ExceptionSpec a [Modifier a] (ExceptionType a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-----------------------------------------------------------------------
-- Expressions

-- | Arguments to methods and constructors are expressions.
type Argument a = (Exp a)

-- | A Java expression.
data Exp a
    -- | A literal denotes a fixed, unchanging value.
    = Lit a (Literal a)
    -- | A class literal, which is an expression consisting of the name of a class, interface, array,
    --   or primitive type, or the pseudo-type void (modelled by 'Nothing'), followed by a `.' and the token class.
    | ClassLit a (Maybe (Type a))
    -- | The keyword @this@ denotes a value that is a reference to the object for which the instance method
    --   was invoked, or to the object being constructed.
    | This a
    -- | Any lexically enclosing instance can be referred to by explicitly qualifying the keyword this.
    | ThisClass a (Name a)
    -- | A parenthesized expression is a primary expression whose type is the type of the contained expression
    --   and whose value at run time is the value of the contained expression. If the contained expression
    --   denotes a variable then the parenthesized expression also denotes that variable.
    | Paren a (Exp a)
    -- | A class instance creation expression is used to create new objects that are instances of classes.
    -- | The first argument is a list of non-wildcard type arguments to a generic constructor.
    --   What follows is the type to be instantiated, the list of arguments passed to the constructor, and
    --   optionally a class body that makes the constructor result in an object of an /anonymous/ class.
    | InstanceCreation a [TypeArgument a] (ClassType a) [Argument a] (Maybe (ClassBody a))
    -- | A qualified class instance creation expression enables the creation of instances of inner member classes
    --   and their anonymous subclasses.
    | QualInstanceCreation a (Exp a) [TypeArgument a] (Ident a) [Argument a] (Maybe (ClassBody a))
    -- | An array instance creation expression is used to create new arrays. The last argument denotes the number
    --   of dimensions that have no explicit length given. These dimensions must be given last.
    | ArrayCreate a (Type a) [(Exp a, Maybe (Policy a))] [Maybe (Policy a)]
    -- | An array instance creation expression may come with an explicit initializer. Such expressions may not
    --   be given explicit lengths for any of its dimensions.
    | ArrayCreateInit a (Type a) [Maybe (Policy a)] (ArrayInit a)
    -- | A field access expression.
    | FieldAccess a (FieldAccess a)
    -- | A method invocation expression.
    | MethodInv a (MethodInvocation a)
    -- | An array access expression refers to a variable that is a component of an array.
    | ArrayAccess a (ArrayIndex a)
    -- | An expression name, e.g. a variable.
    | ExpName a (Name a)
    -- | Post-incrementation expression, i.e. an expression followed by @++@.
    | PostIncrement a (Exp a)
    -- | Post-decrementation expression, i.e. an expression followed by @--@.
    | PostDecrement a (Exp a)
    -- | Pre-incrementation expression, i.e. an expression preceded by @++@.
    | PreIncrement  a (Exp a)
    -- | Pre-decrementation expression, i.e. an expression preceded by @--@.
    | PreDecrement  a (Exp a)
    -- | Unary plus, the promotion of the value of the expression to a primitive numeric type.
    | PrePlus  a (Exp a)
    -- | Unary minus, the promotion of the negation of the value of the expression to a primitive numeric type.
    | PreMinus a (Exp a)
    -- | Unary bitwise complementation: note that, in all cases, @~x@ equals @(-x)-1@.
    | PreBitCompl a (Exp a)
    -- | Logical complementation of boolean values.
    | PreNot  a (Exp a)
    -- | A cast expression converts, at run time, a value of one numeric type to a similar value of another
    --   numeric type; or confirms, at compile time, that the type of an expression is boolean; or checks,
    --   at run time, that a reference value refers to an object whose class is compatible with a specified
    --   reference type.
    | Cast a (Type a) (Exp a)
    -- | The application of a binary operator to two operand expressions.
    | BinOp a (Exp a) (Op a) (Exp a)
    -- | Testing whether the result of an expression is an instance of some reference type.
    | InstanceOf a (Exp a) (RefType a)
    -- | The conditional operator @? :@ uses the boolean value of one expression to decide which of two other
    --   expressions should be evaluated.
    | Cond a (Exp a) (Exp a) (Exp a)
    -- | Assignment of the result of an expression to a variable.
    | Assign a (Lhs a) (AssignOp a) (Exp a)

-- Paragon
    | PolicyExp a (PolicyExp a)
--    | PolicyOf (Ident a)
    | LockExp a (Lock a)

-- Quasi-quotation
    | AntiQExp a String

  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A literal denotes a fixed, unchanging value.
data Literal  a
    = Int     a Integer
    | Word    a Integer
    | Float   a Double
    | Double  a Double
    | Boolean a Bool
    | Char    a Char
    | String  a String
    | Null    a
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A binary infix operator.
data Op a
    = Mult a | Div a | Rem a | Add a | Sub a
    | LShift a | RShift a | RRShift a
    | LThan a | GThan a | LThanE a | GThanE a | Equal a | NotEq a
    | And a | Or a | Xor a | CAnd a | COr a
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | An assignment operator.
data AssignOp a
    = EqualA a
    | MultA a | DivA a | RemA a | AddA a | SubA a
    | LShiftA a | RShiftA a | RRShiftA a
    | AndA a | XorA a | OrA a
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | The left-hand side of an assignment expression. This operand may be a named variable, such as a local
--   variable or a field of the current object or class, or it may be a computed variable, as can result from
--   a field access or an array access.
data Lhs a
    = NameLhs a (Name a)          -- ^ Assign to a variable
    | FieldLhs a (FieldAccess a)  -- ^ Assign through a field access
    | ArrayLhs a (ArrayIndex  a)  -- ^ Assign to an array
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | Array access
data ArrayIndex a = ArrayIndex a (Exp a) (Exp a)    -- ^ Index into an array
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A field access expression may access a field of an object or array, a reference to which is the value
--   of either an expression or the special keyword super.
data FieldAccess a
    = PrimaryFieldAccess a (Exp a) (Ident a)     -- ^ Accessing a field of an object or array computed from an expression.
    | SuperFieldAccess   a (Ident a)             -- ^ Accessing a field of the superclass.
    | ClassFieldAccess   a (Name a) (Ident a)    -- ^ Accessing a (static) field of a named class.
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-- | A method invocation expression is used to invoke a class or instance method.
data MethodInvocation a
    -- | Invoking a specific named method.
    = MethodCallOrLockQuery a (Name a) [Argument a]
    -- | Invoking a method of a class computed from a primary expression, giving arguments for any generic type parameters.
    | PrimaryMethodCall a (Exp a) [NonWildTypeArgument a] (Ident a) [Argument a]
    -- | Invoking a method of the super class, giving arguments for any generic type parameters.
    | SuperMethodCall a [NonWildTypeArgument a] (Ident a) [Argument a]
    -- | Invoking a method of the superclass of a named class, giving arguments for any generic type parameters.
    | ClassMethodCall a (Name a) [NonWildTypeArgument a] (Ident a) [Argument a]
    -- | Invoking a method of a named type, giving arguments for any generic type parameters.
    | TypeMethodCall a (Name a) [NonWildTypeArgument a] (Ident a) [Argument a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | An array initializer may be specified in a declaration, or as part of an array creation expression, creating an
--   array and providing some initial values
data ArrayInit a
    = ArrayInit a [VarInit a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-----------------------------------------------------------------------
-- Types

data ReturnType a
    = VoidType a
    | LockType a
    | Type a (Type a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | There are two kinds of types in the Java programming language: primitive types and reference types.
data Type a
    = PrimType a (PrimType a)
    | RefType a (RefType a)
    | AntiQType a String
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | There are three kinds of reference types: class types, interface types, and array types.
--   Reference types may be parameterized with type arguments.
--   Type variables are introduced by generic type parameters.
data RefType a
    = ClassRefType a (ClassType a)
    | TypeVariable a (Ident a)
    | ArrayType a (Type a) [Maybe (Policy a)]
    -- ^ The second argument to ArrayType is the base type, and should not be an array type
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A class or interface type consists of a type declaration specifier,
--   optionally followed by type arguments (in which case it is a parameterized type).
data ClassType a
    = ClassType a (Name a) [TypeArgument a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | Type arguments may be either reference types or wildcards.
data TypeArgument a
    = Wildcard  a (Maybe (WildcardBound a))
    | ActualArg a (NonWildTypeArgument a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

data NonWildTypeArgument a
    = ActualName a (Name a)      -- Can mean a type or an exp
    | ActualType a (RefType a)
    | ActualExp a (Exp a)        -- Constrained to argExp
    | ActualLockState a [Lock a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-- | Wildcards may be given explicit bounds, either upper (@extends@) or lower (@super@) bounds.
data WildcardBound a
    = ExtendsBound a (RefType a)
    | SuperBound a (RefType a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A primitive type is predefined by the Java programming language and named by its reserved keyword.
data PrimType  a
    = BooleanT a
    | ByteT    a
    | ShortT   a
    | IntT     a
    | LongT    a
    | CharT    a
    | FloatT   a
    | DoubleT  a
-- Paragon
    | ActorT   a
    | PolicyT  a
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

aOfPrimType :: PrimType a -> a
aOfPrimType (BooleanT x) = x
aOfPrimType (ByteT x)    = x
aOfPrimType (ShortT x)   = x
aOfPrimType (IntT x)     = x
aOfPrimType (LongT x)    = x
aOfPrimType (CharT x)    = x
aOfPrimType (FloatT x)   = x
aOfPrimType (DoubleT x)  = x
aOfPrimType (ActorT x)   = x
aOfPrimType (PolicyT x)  = x

-- | A class is generic if it declares one or more type variables. These type variables are known
--   as the type parameters of the class.
--   Paragon adds three new forms - actor, policy and lockstate parameters.
data TypeParam a = TypeParam a (Ident a) [RefType a]
-- Paragon
                 | ActorParam     a (RefType a) (Ident a)
                 | PolicyParam    a (Ident a)
                 | LockStateParam a (Ident a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-----------------------------------------------------------------------
-- Paragon

type Policy a = Exp a

-- | A policy is a conjunction (set) of clauses, represented as a list.
--data PolicyLit = PolicyLit [Clause Actor]
data PolicyExp a = PolicyLit a [Clause a]
                 | PolicyOf  a (Ident a)
                 | PolicyThis a
                 | PolicyTypeVar a (Ident a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-- | A lock property is a potentially recursive policy with an atom head.
data LockProperties a = LockProperties a [LClause a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


-- HERE
-- | A clause of the form Sigma => a, where a is an actor and Sigma a set of
--   locks/atomic predicates that must be open/true.
data Clause a = Clause a [ClauseVarDecl a] (ClauseHead a) [Atom a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

data ClauseVarDecl a = ClauseVarDecl a (RefType a) (Ident a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

data ClauseHead a = ClauseDeclHead a (ClauseVarDecl a)
                  | ClauseVarHead a (Actor a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)


data LClause a = LClause a [ClauseVarDecl a] (Atom a) [Atom a]
               | ConstraintClause a [ClauseVarDecl a] [Atom a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | An actor variable, either forall-quantified within the current clause, or
--   free and thus concrete w.r.t. the policy under scrutiny.
data Actor a = Actor a (ActorName a)    -- ^ Free actor variables
             | Var   a (Ident a)        -- ^ Quantified actor variables
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

data ActorName a
    = ActorName a (Name a)
    -- ^ A free actor variable
    | ActorTypeVar a (RefType a) (Ident a)
    -- ^ A free actor type parameter
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | A lock is an atomic n-ary predicate.
data Atom a = Atom a (Name a) [Actor a]
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

data Lock a = Lock a (Name a) [ActorName a] | LockVar a (Ident a)
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-----------------------------------------------------------------------
-- Useful accessors

importDeclName :: ImportDecl a -> Name a
importDeclName (SingleTypeImport     _ n)   = n
importDeclName (TypeImportOnDemand   _ n)   = n
importDeclName (SingleStaticImport   _ n _) = n
importDeclName (StaticImportOnDemand _ n)   = n


-----------------------------------------------------------------------
-- Names and identifiers

-- | A single identifier.
data Ident a = Ident a B.ByteString | AntiQIdent a String
  deriving (Eq,Ord,Show,Typeable,Data,Functor)

-- | Extract actual identifier string from Ident wrapper type
unIdent :: Ident a -> B.ByteString
unIdent (Ident _ bs) = bs
unIdent (AntiQIdent _ str) = panic (syntaxModule ++ ".unIdent")
            $ "AntiQIdent " ++ str

-- | A name, i.e. a period-separated list of identifiers.
data Name a = Name a NameType (Maybe (Name a)) (Ident a)
            | AntiQName a String
-- Show removed to get more readable debug output
  deriving (Eq,Ord,Typeable,Data,Functor)

-- Prints name as a simple string to be easier to read.
-- To get printout of the whole recursive name structure, comment this out and put
-- Show in the deriving clause.
instance Show (Name a) where
  show (Name _ _ nextBase (Ident _ iBase)) =
    show (showInner nextBase ++ B.unpack iBase)
    where
      showInner Nothing = ""
      showInner (Just (Name _ _ next (Ident _ i))) =  showInner next ++ B.unpack i ++ "."


data NameType
    = EName    -- ^Expression name
    | MName    -- ^Method name
    | TName    -- ^Type (class, interface, enum [not implemented]) name
    | PName    -- ^Package name
    | LName    -- ^Lock name
    | POrTName -- ^Either package or Type name
    | MOrLName -- ^Method or lock name
    | EOrLName -- ^Expression or lock name
    | AmbName  -- ^Ambiguous name
  deriving (Eq,Ord,Show,Typeable,Data)

nameType :: Name a -> NameType
nameType (Name _ nt _ _) = nt
nameType _ = panic (syntaxModule ++ ".nameType")
                   "AntiQName"

setNameType :: NameType -> Name a -> Name a
setNameType nt (Name a _ mPre i) = Name a nt mPre i
setNameType _ n = n

mkSimpleName :: NameType -> Ident a -> Name a
mkSimpleName nt i = Name (ann i) nt Nothing i

mkUniformName :: (a -> a -> a) -- Merge annotations
              -> NameType -> [Ident a] -> Name a
mkUniformName f nt ids = mkName' (reverse ids)
    where mkName' [] = panic (syntaxModule ++ ".mkUniformName")
                             "Empty list of idents"
          mkName' [i] = Name (ann i) nt Nothing i
          mkName' (i:is) =
              let pre = mkName' is
                  a = f (ann pre) (ann i)
              in Name a nt (Just pre) i

mkUniformName_ :: NameType -> [Ident a] -> Name a
mkUniformName_ = mkUniformName const

mkName :: (a -> a -> a) -- Merge annotations
       -> NameType -> NameType -> [Ident a] -> Name a
mkName f nt ntPre ids = mkName' (reverse ids)
    where mkName' [] = panic (syntaxModule ++ ".mkName")
                             "Empty list of idents"
          mkName' [i] = Name (ann i) nt Nothing i
          mkName' (i:is) =
              let pre = mkUniformName f ntPre (reverse is)
                  a = f (ann pre) (ann i)
              in Name a nt (Just pre) i

mkName_ :: NameType -> NameType -> [Ident a] -> Name a
mkName_ = mkName const

flattenName :: Name a -> [Ident a]
flattenName n = reverse $ flName n
    where flName (Name _ _ mPre i) = i : maybe [] flName mPre

          flName AntiQName{} = panic (syntaxModule ++ ".flattenName")
                                     "Cannot flatten name anti-quote"

mkIdent :: a -> String -> Ident a
mkIdent a = Ident a . B.pack

mkIdent_ :: String -> Ident SourcePos
mkIdent_ = mkIdent defaultPos

-----------------------------------------------------------------------
-- Annotations

$(deriveAnnMany
  [''CompilationUnit, ''PackageDecl, ''ImportDecl,
   ''TypeDecl, ''ClassDecl, ''ClassBody, ''EnumBody, ''EnumConstant,
   ''InterfaceDecl, ''InterfaceBody, ''Decl, ''MemberDecl,
   ''VarDecl, ''VarDeclId, ''VarInit, ''ArrayInit,
   ''FormalParam, ''MethodBody, ''ConstructorBody, ''ExplConstrInv,
   ''Modifier, ''Block, ''BlockStmt, ''Stmt,
   ''Catch, ''SwitchBlock, ''SwitchLabel, ''ForInit, ''ExceptionSpec,
   ''Exp, ''Literal, ''Op, ''AssignOp, ''Lhs,
   ''ArrayIndex, ''FieldAccess, ''MethodInvocation,
   ''Type, ''PrimType, ''RefType, ''ClassType, ''ReturnType,
   ''TypeArgument, ''NonWildTypeArgument, ''WildcardBound, ''TypeParam,
   ''PolicyExp, ''LockProperties, ''Clause, ''LClause,
   ''ClauseVarDecl, ''ClauseHead,
   ''Actor, ''ActorName, ''Atom, ''Lock, ''Ident, ''Name])
