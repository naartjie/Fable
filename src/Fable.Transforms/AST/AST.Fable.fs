namespace rec Fable.AST.Fable

open Fable.AST

type EntityRef =
    { QualifiedName: string
      SourcePath: string option }
    member this.FullName =
        let fullName =
            match this.QualifiedName.IndexOf(",") with
            | i when i > 0 -> this.QualifiedName.[..i-1]
            | _ -> this.QualifiedName
        fullName.Replace("+", ".")

type DeclaredType =
    abstract Definition: EntityRef
    abstract GenericArgs: Type list

type Attribute =
    abstract FullName: string
    abstract ConstructorArguments: obj list

type Field =
    abstract Name: string
    abstract FieldType: Type
    abstract IsMutable: bool
    abstract IsStatic: bool
    abstract LiteralValue: obj option

type UnionCase =
    abstract Name: string
    abstract CompiledName: string option
    abstract UnionCaseFields: Field list

type GenericParam =
    abstract Name: string

type Parameter =
    abstract Name: string option
    abstract Type: Type

type MemberInfo =
    abstract Attributes: Attribute seq
    abstract HasSpread: bool
    abstract IsMangled: bool
    abstract IsPublic: bool
    abstract IsInstance: bool
    abstract IsValue: bool
    abstract IsMutable: bool
    abstract IsGetter: bool
    abstract IsSetter: bool
    abstract IsEnumerator: bool

type MemberFunctionOrValue =
    inherit MemberInfo
    abstract DisplayName: string
    abstract CompiledName: string
    abstract FullName: string
    abstract CurriedParameterGroups: Parameter list list
    abstract ReturnParameter: Parameter
    abstract IsExplicitInterfaceImplementation: bool
    abstract ApparentEnclosingEntity: EntityRef

type Entity =
    abstract Ref: EntityRef
    abstract DisplayName: string
    abstract FullName: string
    abstract Attributes: Attribute seq
    abstract BaseDeclaration: DeclaredType option
    abstract AllInterfaces: DeclaredType seq
    abstract GenericParameters: GenericParam list
    abstract MembersFunctionsAndValues: MemberFunctionOrValue seq
    abstract FSharpFields: Field list
    abstract UnionCases: UnionCase list
    abstract IsPublic: bool
    abstract IsFSharpUnion: bool
    abstract IsFSharpRecord: bool
    abstract IsValueType: bool
    abstract IsFSharpExceptionDeclaration: bool
    abstract IsInterface: bool

type Type =
    | MetaType
    | Any
    | Unit
    | Boolean
    | Char
    | String
    | Regex
    | Number of NumberKind
    | Enum of EntityRef
    | Option of genericArg: Type
    | Tuple of genericArgs: Type list
    | Array of genericArg: Type
    | List of genericArg: Type
    | LambdaType of Type * returnType: Type
    | DelegateType of Type list * returnType: Type
    | GenericParam of name: string
    | DeclaredType of EntityRef * genericArgs: Type list
    | AnonymousRecordType of fieldNames: string [] * genericArgs: Type list

    member this.Generics =
        match this with
        | Option gen
        | Array gen
        | List gen -> [ gen ]
        | LambdaType(argType, returnType) -> [ argType; returnType ]
        | DelegateType(argTypes, returnType) -> argTypes @ [ returnType ]
        | Tuple gen -> gen
        | DeclaredType (_, gen) -> gen
        | AnonymousRecordType (_, gen) -> gen
        | _ -> []

type ActionDecl = {
    Body: Expr
    UsedNames: Set<string>
}

type MemberDecl = {
    Name: string
    Args: Ident list
    Body: Expr
    Info: MemberInfo
    UsedNames: Set<string>
}

type ClassDecl = {
    Name: string
    Entity: EntityRef
    Constructor: MemberDecl option
    BaseCall: Expr option
    AttachedMembers: MemberDecl list
}

type Declaration =
    | ActionDeclaration of ActionDecl
    | MemberDeclaration of MemberDecl
    | ClassDeclaration of ClassDecl
    member this.UsedNames =
        match this with
        | ActionDeclaration d -> d.UsedNames
        | MemberDeclaration d -> d.UsedNames
        | ClassDeclaration d ->
            d.Constructor
            |> Option.map (fun c -> c.UsedNames)
            |> Option.defaultValue Set.empty
            |> fun usedNames -> usedNames, d.AttachedMembers
            ||> List.fold (fun acc m -> Set.union acc m.UsedNames)

type File(decls, ?usedRootNames) =
    member __.Declarations: Declaration list = decls
    member __.UsedNamesInRootScope: Set<string> = defaultArg usedRootNames Set.empty

type Ident =
    { Name: string
      Type: Type
      IsMutable: bool
      IsThisArgument: bool
      IsCompilerGenerated: bool
      Range: SourceLocation option }
    member x.DisplayName =
        x.Range
        |> Option.bind (fun r -> r.identifierName)
        |> Option.defaultValue x.Name

type ValueKind =
    // The AST from F# compiler is a bit inconsistent with ThisValue and BaseValue.
    // ThisValue only appears in constructors and not in instance members (where `this` is passed as first argument)
    // BaseValue can appear both in constructor and instance members (where they're associated to this arg)
    | ThisValue of Type
    | BaseValue of boundIdent: Ident option * Type
    | TypeInfo of Type
    | Null of Type
    | UnitConstant
    | BoolConstant of bool
    | CharConstant of char
    | StringConstant of string
    | NumberConstant of float * NumberKind
    | RegexConstant of source: string * flags: RegexFlag list
    | EnumConstant of Expr * EntityRef
    | NewOption of value: Expr option * Type
    | NewArray of Expr list * Type
    | NewArrayFrom of Expr * Type
    | NewList of headAndTail: (Expr * Expr) option * Type
    | NewTuple of Expr list
    | NewRecord of Expr list * EntityRef * genArgs: Type list
    | NewAnonymousRecord of Expr list * fieldNames: string [] * genArgs: Type list
    | NewUnion of Expr list * tag: int * EntityRef * genArgs: Type list
    member this.Type =
        match this with
        | ThisValue t
        | BaseValue(_,t) -> t
        | TypeInfo _ -> MetaType
        | Null t -> t
        | UnitConstant -> Unit
        | BoolConstant _ -> Boolean
        | CharConstant _ -> Char
        | StringConstant _ -> String
        | NumberConstant (_, kind) -> Number kind
        | RegexConstant _ -> Regex
        | EnumConstant (_, ent) -> Enum ent
        | NewOption (_, t) -> Option t
        | NewArray (_, t) -> Array t
        | NewArrayFrom (_, t) -> Array t
        | NewList (_, t) -> List t
        | NewTuple exprs -> exprs |> List.map (fun e -> e.Type) |> Tuple
        | NewRecord (_, ent, genArgs) -> DeclaredType(ent, genArgs)
        | NewAnonymousRecord (_, fieldNames, genArgs) -> AnonymousRecordType(fieldNames, genArgs)
        | NewUnion (_, _, ent, genArgs) -> DeclaredType(ent, genArgs)

type CallInfo =
    { ThisArg: Expr option
      Args: Expr list
      /// Argument types as defined in the method signature, this may be slightly different to types of actual argument expressions.
      /// E.g.: signature accepts 'a->'b->'c (2-arity) but we pass int->int->int->int (3-arity)
      SignatureArgTypes: Type list
      HasSpread: bool
      IsJsConstructor: bool }

type ReplaceCallInfo =
    { CompiledName: string
      OverloadSuffix: string
      /// See ArgInfo.SignatureArgTypes
      SignatureArgTypes: Type list
      HasSpread: bool
      IsModuleValue: bool
      IsInterface: bool
      DeclaringEntityFullName: string
      GenericArgs: (string * Type) list }

type EmitInfo =
    { Macro: string
      IsJsStatement: bool
      CallInfo: CallInfo }

type ImportInfo =
    { Selector: Expr
      Path: Expr
      IsCompilerGenerated: bool }

type OperationKind =
    | Unary of UnaryOperator * Expr
    | Binary of BinaryOperator * left: Expr * right: Expr
    | Logical of LogicalOperator * left: Expr * right: Expr

type KeyKind =
    | FieldKey of Field
    | ExprKey of Expr

type GetKind =
    | ByKey of KeyKind
    | TupleIndex of int
    | UnionField of index: int * fieldType: Type
    | UnionTag
    | ListHead
    | ListTail
    | OptionValue

type TestKind =
    | TypeTest of Type
    | OptionTest of isSome: bool
    | ListTest of isCons: bool
    | UnionCaseTest of tag: int

type Expr =
    // Values and Idents
    | Value of ValueKind * SourceLocation option
    | IdentExpr of Ident

    // Closures
    /// Lambdas are curried, they always have a single argument (which can be unit)
    | Lambda of arg: Ident * body: Expr * name: string option
    /// Delegates are uncurried functions, can have none or multiple arguments
    | Delegate of args: Ident list * body: Expr * name: string option
    | ObjectExpr of MemberDecl list * Type * baseCall: Expr option

    // Type cast and tests
    | TypeCast of Expr * Type
    | Test of Expr * TestKind * range: SourceLocation option

    // Operations
    | Call of callee: Expr * info: CallInfo * typ: Type * range: SourceLocation option
    | CurriedApply of applied: Expr * args: Expr list * typ: Type * range: SourceLocation option
    | Curry of Expr * arity: int * Type * SourceLocation option
    | Operation of OperationKind * typ: Type * range: SourceLocation option

    // JS related: imports and statements
    | Import of ImportInfo * Type * SourceLocation option
    | Emit of EmitInfo * Type * SourceLocation option

    // Pattern matching
    | DecisionTree of Expr * targets: (Ident list * Expr) list
    | DecisionTreeSuccess of targetIndex: int * boundValues: Expr list * Type

    // Getters, setters and bindings
    | Let of bindings: (Ident * Expr) list * body: Expr
    | Get of Expr * GetKind * typ: Type * range: SourceLocation option
    | Set of Expr * key: KeyKind option * value: Expr * range: SourceLocation option

    // Control flow
    | Sequential of Expr list
    | WhileLoop of guard: Expr * body: Expr * range: SourceLocation option
    | ForLoop of ident: Ident * start: Expr * limit: Expr * body: Expr * isUp: bool * range: SourceLocation option
    | TryCatch of body: Expr * catch: (Ident * Expr) option * finalizer: Expr option * range: SourceLocation option
    | IfThenElse of guardExpr: Expr * thenExpr: Expr * elseExpr: Expr * range: SourceLocation option

    member this.Type =
        match this with
        | Test _ -> Boolean
        | Value (kind, _) -> kind.Type
        | IdentExpr id -> id.Type
        | Call(_,_,t,_)
        | CurriedApply(_,_,t,_)
        | TypeCast (_, t)
        | Import (_, t, _)
        | Curry (_, _, t, _)
        | ObjectExpr (_, t, _)
        | Operation (_, t, _)
        | Get (_, _, t, _)
        | Emit (_,t,_)
        | DecisionTreeSuccess (_, _, t) -> t
        | Set _
        | WhileLoop _
        | ForLoop _-> Unit
        | Sequential exprs -> List.tryLast exprs |> Option.map (fun e -> e.Type) |> Option.defaultValue Unit
        | Let (_, expr)
        | TryCatch (expr, _, _, _)
        | IfThenElse (_, expr, _, _)
        | DecisionTree (expr, _) -> expr.Type
        | Lambda(arg, body, _) -> LambdaType(arg.Type, body.Type)
        | Delegate(args, body, _) -> DelegateType(args |> List.map (fun a -> a.Type), body.Type)

    member this.Range: SourceLocation option =
        match this with
        | ObjectExpr _
        | Sequential _
        | Let _
        | DecisionTree _
        | DecisionTreeSuccess _ -> None
        | Lambda (_, e, _)
        | Delegate (_, e, _)
        | TypeCast (e, _) -> e.Range
        | IdentExpr id -> id.Range
        | Call(_,_,_,r)
        | CurriedApply(_,_,_,r)
        | Emit (_,_,r)
        | Import(_,_,r)
        | Curry(_,_,_,r)
        | Value (_, r)
        | IfThenElse (_, _, _, r)
        | TryCatch (_, _, _, r)
        | Test (_, _, r)
        | Operation (_, _, r)
        | Get (_, _, _, r)
        | Set (_, _, _, r)
        | ForLoop (_,_,_,_,_,r)
        | WhileLoop (_,_,r) -> r
