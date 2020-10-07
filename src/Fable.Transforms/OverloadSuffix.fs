[<RequireQualifiedAccess>]
module rec Fable.Transforms.OverloadSuffix

open Fable
open Fable.AST
open System.Collections.Generic

let private hashToString (i: int) =
    if i < 0
    then "Z" + (abs i).ToString("X")
    else i.ToString("X")

let private getGenericConstraintHash genParams (c: Fable.GenericConstraint) =
    match c with
    | Fable.MayResolveMember i ->
         // TODO: Full member signature hash?
         "" + (if i.IsStatic then "static " else "") + "member " + i.Name
    | Fable.IsEnum -> "enum"
    | Fable.CoercesTo t -> ":>" + (getTypeFastFullName genParams t)
    | Fable.SupportsNull -> "null"
    | Fable.RequiresDefaultConstructor -> "new"
    | Fable.IsNonNullableStruct -> "struct"
    | Fable.IsReferenceType -> "not struct"
    | Fable.SupportsComparison -> "comparison"
    | Fable.SupportsEquality -> "equality"

let rec private getTypeFastFullName (genParams: IDictionary<_,_>) (t: Fable.Type) =
    match t with
    | Fable.MetaType -> Types.type_
    | Fable.Any -> Types.object
    | Fable.Unit -> Types.unit
    | Fable.Boolean -> Types.bool
    | Fable.Char -> Types.char
    | Fable.String -> Types.string
    | Fable.Regex -> Types.regex
    | Fable.Number kind ->
        Types.numberKind
        |> Seq.tryFind (fun kv -> kv.Value = kind)
        |> function Some kv -> kv.Key | None -> "number"
    | Fable.Enum ent -> ent
    | Fable.Tuple gen -> gen |> List.map (getTypeFastFullName genParams) |> String.concat " * "
    | Fable.Array gen -> getTypeFastFullName genParams gen + "[]"
    | Fable.List gen -> getTypeFastFullName genParams gen + " list"
    | Fable.Option gen -> getTypeFastFullName genParams gen + " option"
    | Fable.LambdaType(gen1, gen2) ->
        getTypeFastFullName genParams gen1 + " -> " + getTypeFastFullName genParams gen2
    | Fable.DelegateType(gen1, gen2) ->
        let gen1 = "(" + (gen1 |> List.map (getTypeFastFullName genParams) |> String.concat ", ") + ") => "
        gen1 + getTypeFastFullName genParams gen2
    | Fable.GenericParam g ->
        match genParams.TryGetValue(g.Name) with
        | true, i -> i
        | false, _ -> "'" + (List.map (getGenericConstraintHash genParams) g.Constraints |> String.concat ",")
    | Fable.AnonymousRecordType(fieldNames, gen) ->
        List.zip fieldNames gen
        |> List.map (fun (key, typ) -> key + " : " + getTypeFastFullName genParams typ)
        |> String.concat "; "
    | Fable.DeclaredType(e, gen) ->
        let gen = gen |> List.map (getTypeFastFullName genParams) |> String.concat ", "
        e + (if gen = "" then "" else "[" + gen + "]")

// From https://stackoverflow.com/a/37449594
let private combineHashCodes (hashes: int seq) =
    let hashes = Seq.toArray hashes
    if hashes.Length = 0
    then 0
    else hashes |> Array.reduce (fun h1 h2 -> ((h1 <<< 5) + h1) ^^^ h2)

// F# hash function gives different results in different runs
// Taken from fable-library/Util.ts. Possible variant in https://stackoverflow.com/a/1660613
let private stringHash (s: string) =
    let mutable h = 5381
    for i = 0 to s.Length - 1 do
        h <- (h * 33) ^^^ (int s.[i])
    h

let [<Literal>] noOverloadSuffix = "Fable.Core.OverloadSuffixAttribute" // typeof<Fable.Core.NoOverloadSuffixAttribute>.FullName

let private getHashPrivate (entAtts: Fable.Attribute list) (paramTypes: Fable.Type list) genParams =
    // This is only needed when compiling fable-library, use conditional compilation?
    if entAtts |> List.exists (fun a -> a.FullName = noOverloadSuffix) then ""
    else
        paramTypes
        |> List.map (getTypeFastFullName genParams >> stringHash)
        |> combineHashCodes
        |> hashToString

let hasEmptyOverloadSuffix (curriedParamTypes: Fable.Type list) =
    // Don't use overload suffix for members without arguments
    match curriedParamTypes with
    | [] -> true
    | [Fable.Unit] -> true
    | _ -> false

let getHash (entity: Fable.Entity) (m: Fable.MemberFunctionOrValue) =
    // Members with curried params cannot be overloaded in F#
    // TODO: Also private methods defined with `let` cannot be overloaded
    // but I don't know how to identify them in the AST
    if not(List.isSingle m.CurriedParameterGroups) then ""
    else
        let paramTypes = m.CurriedParameterGroups.[0] |> Seq.map (fun p -> p.Type) |> Seq.toList
        if hasEmptyOverloadSuffix paramTypes then ""
        else
            // Generics can have different names in signature
            // and implementation files, use the position instead
            let genParams =
                entity.GenericParameters
                |> Seq.mapi (fun i p -> p.Name, string i)
                |> dict
            getHashPrivate m.Attributes paramTypes genParams

//let getAbstractSignatureHash (entity: Fable.Entity) (m: FSharpAbstractSignature) =
//    // Members with curried params cannot be overloaded in F#
//    if m.AbstractArguments.Count <> 1 then ""
//    else
//        let paramTypes = m.AbstractArguments.[0] |> Seq.map (fun p -> p.Type) |> Seq.toList
//        if hasEmptyOverloadSuffix paramTypes then ""
//        else
//            // Generics can have different names in signature
//            // and implementation, use the position instead
//            let genParams =
//                entity.GenericParameters
//                |> Seq.mapi (fun i p -> p.Name, string i)
//                |> dict
//            getHashPrivate [||] paramTypes genParams

/// Used for extension members
let getExtensionHash (m: Fable.MemberFunctionOrValue) =
    // Members with curried params cannot be overloaded in F#
    if not(List.isSingle m.CurriedParameterGroups) then ""
    else
        let paramTypes = m.CurriedParameterGroups.[0] |> Seq.map (fun p -> p.Type) |> Seq.toList
        if hasEmptyOverloadSuffix paramTypes then ""
        else
            // Type resolution in extension member seems to be different
            // and doesn't take generics into account
            dict [] |> getHashPrivate m.Attributes paramTypes
