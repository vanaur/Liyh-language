namespace Liyh.Semantic

open System

/// Implements the rational arithmetic for dimensional analysis.
[<CustomComparison; CustomEquality>]
type public Rational =
    { Num: int
      Den: int }

    static member Create(n: int, d: int) =
        if d = 0 then invalidArg (nameof d) "Division by zero"

        let rec gcd a b = if b = 0 then abs a else gcd b (a % b)

        let g = gcd n d
        let sign = if d < 0 then -1 else 1

        { Num = sign * (n / g)
          Den = abs (d / g) }

    static member Zero = Rational.Create(0, 1)
    static member One = Rational.Create(1, 1)
    static member Half = Rational.Create(1, 2)

    static member ( + ) (a, b) = Rational.Create(a.Num * b.Den + b.Num * a.Den, a.Den * b.Den)
    static member ( - ) (a, b) = Rational.Create(a.Num * b.Den - b.Num * a.Den, a.Den * b.Den)
    static member ( * ) (a, b) = Rational.Create(a.Num * b.Num, a.Den * b.Den)
    static member ( / ) (a, b) = Rational.Create(a.Num * b.Den, a.Den * b.Num)

    override this.ToString() =
        if this.Den = 1 then string this.Num
        else sprintf "%d/%d" this.Num this.Den

    override this.Equals(obj) =
        match obj with
        | :? Rational as r -> this.Num = r.Num && this.Den = r.Den
        | _ -> false

    override this.GetHashCode() = hash (this.Num, this.Den)

    interface IComparable with
        member this.CompareTo(obj) =
            match obj with
            | :? Rational as r -> compare (this.Num * r.Den) (r.Num * this.Den)
            | _ -> invalidArg (nameof obj) "Incompatible type"

/// Like a type variable, a `DimVar` plays the role as a type variable for dimensions.
/// A dimension variable is either unbound or linked. This representation with
/// two constructors is used for mutable in-place modifications while unifying.
type public DimVar =
    | UnboundDim of string
    | LinkDim of Dimension

and public DimAtom =
    | DimBase of string         // Arbitrary generator: "Mass", "Length", "Data", "Currency", ...
    | DimVar of DimVar ref      // Free variable: 'd1, 'd2, ...

and public Dimension = Map<DimAtom, Rational>

module public Dimension =
    let public empty : Dimension = Map.empty

    /// Removes chains of dim variables.
    let rec public prune (d: Dimension) : Dimension =
        let mutable result = Map.empty

        for KeyValue(atom, coeff) in d do
            match atom with
            | DimVar ({ contents = LinkDim linked } as r) ->
                let prunedLinked = prune linked
                r.Value <- LinkDim prunedLinked

                for KeyValue(innerAtom, innerCoeff) in prunedLinked do
                    let newCoeff = innerCoeff * coeff

                    match Map.tryFind innerAtom result with
                    | Some c -> result <- Map.add innerAtom (c + newCoeff) result
                    | None   -> result <- Map.add innerAtom newCoeff result

            | _ ->
                match Map.tryFind atom result with
                | Some c -> result <- Map.add atom (c + coeff) result
                | None   -> result <- Map.add atom coeff result

        Map.filter (fun _ (r: Rational) -> r.Num <> 0) result

    /// Multiplies two dimentionned values: `L^a ⋅ L^b = L^(a+b)`.
    let public mul (d1: Dimension) (d2: Dimension) : Dimension =
        let p1 = prune d1
        let p2 = prune d2

        Map.fold (fun acc k v ->
            match Map.tryFind k acc with
            | Some v' -> Map.add k (v' + v) acc
            | None -> Map.add k v acc
        ) p1 p2 |> prune

    /// Divides two dimentionned values: `L^a / L^b = L^(a - b)`.
    let public div (d1: Dimension) (d2: Dimension) : Dimension =
        let invD2 = Map.map (fun _ r -> Rational.Create(-r.Num, r.Den)) (prune d2)
        mul d1 invD2

    /// Raises a dimensionned value to a rational power: `(L^d)^r = L^(d ⋅ r)`.
    let public scale (r: Rational) (d: Dimension) : Dimension =
        prune d |> Map.map (fun _ coeff -> coeff * r) |> prune

    /// Returns a string representation of the dimension.
    let rec public toString (d: Dimension) =
        let cleaned = prune d

        if Map.isEmpty cleaned then "1"
        else
            cleaned
            |> Map.toList
            |> List.map (fun (atom, exp) ->
                let name =
                    match atom with
                    | DimBase s -> s
                    | DimVar r ->
                        match r.contents with
                        | UnboundDim name -> sprintf "'%s" name
                        | LinkDim d -> toString d

                if exp = Rational.One then name else sprintf "%s^%s" name (string exp))
            |> String.concat " ⋅ "

