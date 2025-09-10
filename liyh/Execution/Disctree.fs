namespace Liyh.Execution

(*

module Disctree =
    open System
    open System.Collections.Generic

    type Term =
        | Var of string
        | Wildcard
        | Const of string
        | App of string * Term list

        override this.ToString() =
            match this with
            | Var v -> v
            | Wildcard -> "_"
            | Const c -> c
            | App(f, args) -> sprintf "%s[%s]" (string f) (System.String.Join(", ", List.map string args))
    
    type Rule =
        { Pattern: Term
          Condition: (Map<string, Term> -> bool)
          Rewrite: Term }

    // Clé de discrimination : soit un symbole exact, soit "VAR" pour une variable
    type DiscKey =
        | Symbol of string
        | Variable
        | WildcardKey

    type DiscriminationTree =
        | Leaf of Rule list  // On garde une liste, mais on insère à la fin pour préserver l'ordre
        | Node of Map<DiscKey, DiscriminationTree>

    module DiscriminationTree =

        // Convertir un terme en séquence de clés de discrimination
        let rec private termToKeys (term: Term) : DiscKey list =
            match term with
            | Var _ -> [Variable]
            | Wildcard -> [WildcardKey]
            | Const c -> [Symbol c]
            | App(f, args) -> Symbol f :: (args |> List.collect termToKeys)

        // Insérer une règle dans l'arbre — en préservant l'ordre (insertion à la fin)
        let rec private insert (rule: Rule) (keys: DiscKey list) (tree: DiscriminationTree) =
            match keys with
            | [] ->
                // Fin du chemin : ajouter la règle à la fin pour préserver l'ordre
                match tree with
                | Leaf rules -> Leaf(rules @ [rule])  // ← insertion à la fin
                | Node _ -> Leaf [rule] // Remplacer le nœud par une feuille
            
            | key :: restKeys ->
                match tree with
                | Leaf rules ->
                    // Transformer la feuille en nœud et continuer
                    let baseNode = Map.empty |> Map.add key (insert rule restKeys (Leaf []))
                    let nodeWithRules = 
                        rules |> List.fold (fun acc r -> 
                            let subtree = acc |> Map.tryFind key |> Option.defaultValue (Leaf [])
                            Map.add key (insert r restKeys subtree) acc
                        ) baseNode
                    Node nodeWithRules
                
                | Node children ->
                    let subtree = children |> Map.tryFind key |> Option.defaultValue (Leaf [])
                    let newSubtree = insert rule restKeys subtree
                    Node(children |> Map.add key newSubtree)

        // Construire l'arbre à partir d'une liste de règles — dans l'ordre donné
        let build (rules: Rule list) =
            rules |> List.fold (fun tree rule -> 
                let keys = termToKeys rule.Pattern
                insert rule keys tree
            ) (Leaf [])

        // Rechercher TOUTES les règles candidates — dans l'ordre de stockage (donc d'insertion)
        let rec private search (keys: DiscKey list) (tree: DiscriminationTree) : Rule list =
            match keys, tree with
            | [], Leaf rules -> rules  // ← déjà dans l'ordre grâce à l'insertion à la fin
            | [], Node _ -> []
            
            | key :: restKeys, Node children ->
                let results = ResizeArray<Rule>()
                
                // Chercher avec la clé exacte
                match children |> Map.tryFind key with
                | Some subtree -> results.AddRange(search restKeys subtree)
                | None -> ()
                
                // Chercher avec Variable (peut matcher n'importe quoi)
                match children |> Map.tryFind Variable with
                | Some subtree -> results.AddRange(search restKeys subtree)
                | None -> ()
                
                results |> Seq.toList
            
            | _, Leaf _ -> []

        // 🔥 NOUVELLE FONCTION : retourne la PREMIÈRE règle qui matche (selon l'ordre de définition)
        let lookupFirst (term: Term) (tree: DiscriminationTree) : Rule option =
            let keys = termToKeys term
            let candidates = search keys tree

            // Parcourir dans l'ordre et retourner la première qui matche vraiment
            candidates |> List.tryPick (fun rule ->
                let rec matches (pattern: Term) (term: Term) (bindings: Map<string, Term>) =
                    match pattern, term with
                    | Var v, t ->
                        match bindings |> Map.tryFind v with
                        | Some existing -> if existing = t then Some bindings else None
                        | None -> Some (bindings |> Map.add v t)
                    
                    | Const c1, Const c2 -> 
                        if c1 = c2 then Some bindings else None
                    
                    | App(f1, args1), App(f2, args2) when f1 = f2 && args1.Length = args2.Length ->
                        let rec matchArgs args1 args2 bindings =
                            match args1, args2 with
                            | [], [] -> Some bindings
                            | p::ps, t::ts ->
                                match matches p t bindings with
                                | Some newBindings -> matchArgs ps ts newBindings
                                | None -> None
                            | _ -> None
                        matchArgs args1 args2 bindings
                    
                    | _ -> None

                match matches rule.Pattern term Map.empty with
                | Some bindings when rule.Condition bindings -> Some rule
                | _ -> None
            )

    let example () =
        let rules =
            [
                // add[0, 'x] -> 'x
                { Pattern = App("add", [ Const "0"; Var "x" ])
                  Condition = fun _ -> true
                  Rewrite = Var "x" }

                // add['x, 0] -> 'x
                { Pattern = App("add", [ Var "x"; Const "0" ])
                  Condition = fun _ -> true
                  Rewrite = Var "x" }

                // add['x, 'x] -> mul[2, 'x]
                { Pattern = App("add", [ Var "x"; Var "x" ])
                  Condition = fun _ -> true
                  Rewrite = App("mul", [ Const "2"; Var "x" ]) }
                
                // is_zero['x] when 'x = 0 -> true   ← doit matcher AVANT la règle générale
                { Pattern = App("is_zero", [ Var "x" ])
                  Condition = fun bindings -> 
                      match bindings |> Map.tryFind "x" with 
                      | Some (Const "0") -> true 
                      | _ -> false
                  Rewrite = Const "true" }

                // is_zero[_] -> false (règle plus générale, définie après)
                { Pattern = App("is_zero", [ Var "y" ])
                  Condition = fun _ -> true
                  Rewrite = Const "false" }
            ]

        let tree = DiscriminationTree.build rules
        
        let test term =
            printfn "testing term: %A" term
            match DiscriminationTree.lookupFirst term tree with
            | Some rule -> printfn "✅ matched rule: %A -> %A" rule.Pattern rule.Rewrite
            | None -> printfn "❌ no matching rule found"

        test <| App("add", [ Const "0"; App("add", [ Const "0"; Const "17" ]) ])

        // test <| App("add", [ Const "0"; Const "17" ])
        // test <| App("add", [ Const "17"; Const "0" ])
        // test <| App("add", [ Const "5"; Const "5" ])
        // test <| App("is_zero", [ Const "0" ])      // ← Doit retourner la règle spécifique (true)
        // test <| App("is_zero", [ Const "42" ])     // ← Doit retourner la règle générale (false)

*)

(*

// Bon ça marche pas trop

module Disctree =
    open System
    open System.Collections.Generic

    type Term =
        | Var of string
        | Wildcard
        | Const of string
        | App of string * Term list

        override this.ToString() =
            match this with
            | Var v -> v
            | Wildcard -> "_"
            | Const c -> c
            | App(f, args) -> sprintf "%s[%s]" (string f) (System.String.Join(", ", List.map string args))

    // Stratégie d'évaluation pour chaque règle individuelle
    type EvaluationStrategy =
        | Innermost  // Cette règle ne s'applique qu'après évaluation des sous-termes
        | Outermost  // Cette règle peut s'appliquer avant l'évaluation des sous-termes
    
    type Rule =
        { Pattern: Term
          Condition: (Map<string, Term> -> bool)
          Rewrite: Term
          Strategy: EvaluationStrategy }

    // Clé de discrimination : soit un symbole exact, soit "VAR" pour une variable
    type DiscKey =
        | Symbol of string
        | Variable
        | WildcardKey

    type DiscriminationTree =
        | Leaf of Rule list  // On garde une liste, mais on insère à la fin pour préserver l'ordre
        | Node of Map<DiscKey, DiscriminationTree>

    module DiscriminationTree =

        // Convertir un terme en séquence de clés de discrimination
        let rec private termToKeys (term: Term) : DiscKey list =
            match term with
            | Var _ -> [Variable]
            | Wildcard -> [WildcardKey]
            | Const c -> [Symbol c]
            | App(f, args) -> Symbol f :: (args |> List.collect termToKeys)

        // Insérer une règle dans l'arbre — en préservant l'ordre (insertion à la fin)
        let rec private insert (rule: Rule) (keys: DiscKey list) (tree: DiscriminationTree) =
            match keys with
            | [] ->
                // Fin du chemin : ajouter la règle à la fin pour préserver l'ordre
                match tree with
                | Leaf rules -> Leaf(rules @ [rule])  // ← insertion à la fin
                | Node _ -> Leaf [rule] // Remplacer le nœud par une feuille
            
            | key :: restKeys ->
                match tree with
                | Leaf rules ->
                    // Transformer la feuille en nœud et continuer
                    let baseNode = Map.empty |> Map.add key (insert rule restKeys (Leaf []))
                    let nodeWithRules = 
                        rules |> List.fold (fun acc r -> 
                            let subtree = acc |> Map.tryFind key |> Option.defaultValue (Leaf [])
                            Map.add key (insert r restKeys subtree) acc
                        ) baseNode
                    Node nodeWithRules
                
                | Node children ->
                    let subtree = children |> Map.tryFind key |> Option.defaultValue (Leaf [])
                    let newSubtree = insert rule restKeys subtree
                    Node(children |> Map.add key newSubtree)

        // Construire l'arbre à partir d'une liste de règles — dans l'ordre donné
        let build (rules: Rule list) =
            rules |> List.fold (fun tree rule -> 
                let keys = termToKeys rule.Pattern
                insert rule keys tree
            ) (Leaf [])

        // Rechercher TOUTES les règles candidates — dans l'ordre de stockage (donc d'insertion)
        let rec private search (keys: DiscKey list) (tree: DiscriminationTree) : Rule list =
            match keys, tree with
            | [], Leaf rules -> rules  // ← déjà dans l'ordre grâce à l'insertion à la fin
            | [], Node _ -> []
            
            | key :: restKeys, Node children ->
                let results = ResizeArray<Rule>()
                
                // Chercher avec la clé exacte
                match children |> Map.tryFind key with
                | Some subtree -> results.AddRange(search restKeys subtree)
                | None -> ()
                
                // Chercher avec Variable (peut matcher n'importe quoi)
                match children |> Map.tryFind Variable with
                | Some subtree -> results.AddRange(search restKeys subtree)
                | None -> ()
                
                results |> Seq.toList
            
            | _, Leaf _ -> []

        // Fonction pour matcher un pattern contre un terme
        let rec private matches (pattern: Term) (term: Term) (bindings: Map<string, Term>) =
            match pattern, term with
            | Var v, t ->
                match bindings |> Map.tryFind v with
                | Some existing -> if existing = t then Some bindings else None
                | None -> Some (bindings |> Map.add v t)
            
            | Const c1, Const c2 -> 
                if c1 = c2 then Some bindings else None
            
            | App(f1, args1), App(f2, args2) when f1 = f2 && args1.Length = args2.Length ->
                let rec matchArgs args1 args2 bindings =
                    match args1, args2 with
                    | [], [] -> Some bindings
                    | p::ps, t::ts ->
                        match matches p t bindings with
                        | Some newBindings -> matchArgs ps ts newBindings
                        | None -> None
                    | _ -> None
                matchArgs args1 args2 bindings
            
            | _ -> None

        // Substituer les variables dans un terme selon les bindings
        let rec private substitute (bindings: Map<string, Term>) (term: Term) : Term =
            match term with
            | Var v -> 
                match bindings |> Map.tryFind v with
                | Some t -> t
                | None -> term
            | Const _ -> term
            | Wildcard -> term
            | App(f, args) -> App(f, args |> List.map (substitute bindings))

        // Chercher les règles d'une stratégie spécifique qui matchent un terme
        let lookupByStrategy (strategy: EvaluationStrategy) (term: Term) (tree: DiscriminationTree) : (Rule * Map<string, Term>) option =
            let keys = termToKeys term
            let candidates = search keys tree

            // Parcourir dans l'ordre et retourner la première règle de la bonne stratégie qui matche
            candidates 
            |> List.filter (fun rule -> rule.Strategy = strategy)
            |> List.tryPick (fun rule ->
                match matches rule.Pattern term Map.empty with
                | Some bindings when rule.Condition bindings -> Some (rule, bindings)
                | _ -> None
            )

        // Chercher toute règle qui matche (indépendamment de la stratégie)
        let lookupFirst (term: Term) (tree: DiscriminationTree) : (Rule * Map<string, Term>) option =
            let keys = termToKeys term
            let candidates = search keys tree

            candidates |> List.tryPick (fun rule ->
                match matches rule.Pattern term Map.empty with
                | Some bindings when rule.Condition bindings -> Some (rule, bindings)
                | _ -> None
            )

        // Appliquer une règle à un terme avec les bindings donnés
        let applyRule (rule: Rule) (bindings: Map<string, Term>) : Term =
            substitute bindings rule.Rewrite

        // Réécriture d'un seul pas en respectant les stratégies individuelles des règles
        let rec rewriteStep (tree: DiscriminationTree) (term: Term) : Term option =
            match term with
            | Var _ | Const _ | Wildcard -> 
                // Pour les feuilles, on cherche toute règle applicable
                match lookupFirst term tree with
                | Some (rule, bindings) -> Some (applyRule rule bindings)
                | None -> None
            
            | App(f, args) ->
                // D'abord essayer les règles OUTERMOST sur le terme courant
                match lookupByStrategy Outermost term tree with
                | Some (rule, bindings) -> 
                    Some (applyRule rule bindings)
                | None ->
                    // Ensuite essayer de réécrire récursivement les arguments (pour les règles innermost)
                    let rec tryRewriteArgs acc remainingArgs =
                        match remainingArgs with
                        | [] -> None  // Aucun argument n'a pu être réécrit
                        | arg :: rest ->
                            match rewriteStep tree arg with
                            | Some newArg -> 
                                // Un argument a été réécrit, reconstruire le terme
                                let newArgs = List.rev acc @ [newArg] @ rest
                                Some (App(f, newArgs))
                            | None -> 
                                // Cet argument n'a pas changé, essayer le suivant
                                tryRewriteArgs (arg :: acc) rest
                    
                    match tryRewriteArgs [] args with
                    | Some newTerm -> Some newTerm
                    | None ->
                        // Si aucun sous-terme n'a changé, essayer les règles INNERMOST sur le terme complet
                        match lookupByStrategy Innermost term tree with
                        | Some (rule, bindings) -> Some (applyRule rule bindings)
                        | None -> None

        // Réécriture jusqu'à forme normale avec limitation du nombre d'étapes
        let rec rewriteToNormalForm (tree: DiscriminationTree) (maxSteps: int) (term: Term) : Term =
            if maxSteps <= 0 then 
                failwith "Maximum number of rewrite steps exceeded - possible infinite loop"
            
            match rewriteStep tree term with
            | Some newTerm -> 
                // Le terme a changé, continuer la réécriture
                rewriteToNormalForm tree (maxSteps - 1) newTerm
            | None -> 
                // Aucune règle ne s'applique, forme normale atteinte
                term

        // Version avec un nombre d'étapes par défaut raisonnable
        let normalize (tree: DiscriminationTree) (term: Term) : Term =
            rewriteToNormalForm tree 1000 term

    let example () =
        let rules =
            [
                // Règles arithmétiques de base - INNERMOST (s'appliquent après simplification des arguments)
                { Pattern = App("add", [ Const "0"; Var "x" ])
                  Condition = fun _ -> true
                  Rewrite = Var "x" 
                  Strategy = Innermost }

                { Pattern = App("add", [ Var "x"; Const "0" ])
                  Condition = fun _ -> true
                  Rewrite = Var "x" 
                  Strategy = Innermost }

                { Pattern = App("add", [ Var "x"; Var "x" ])
                  Condition = fun _ -> true
                  Rewrite = App("mul", [ Const "2"; Var "x" ]) 
                  Strategy = Innermost }
                  
                { Pattern = App("mul", [ Const "1"; Var "x" ])
                  Condition = fun _ -> true
                  Rewrite = Var "x"
                  Strategy = Innermost }
                  
                { Pattern = App("mul", [ Var "x"; Const "1" ])
                  Condition = fun _ -> true
                  Rewrite = Var "x"
                  Strategy = Innermost }

                { Pattern = App("mul", [ Const "0"; Var "x" ])
                  Condition = fun _ -> true
                  Rewrite = Const "0"
                  Strategy = Innermost }
                  
                // Règle de court-circuit - OUTERMOST (peut s'appliquer sans évaluer les arguments)
                { Pattern = App("and", [ Const "false"; Var "x" ])
                  Condition = fun _ -> true
                  Rewrite = Const "false" 
                  Strategy = Outermost }
                  
                { Pattern = App("and", [ Var "x"; Const "false" ])
                  Condition = fun _ -> true
                  Rewrite = Const "false" 
                  Strategy = Outermost }
                
                // Test conditionnel - OUTERMOST pour éviter d'évaluer les branches inutiles
                { Pattern = App("if", [ Const "true"; Var "then"; Var "else" ])
                  Condition = fun _ -> true
                  Rewrite = Var "then" 
                  Strategy = Outermost }
                  
                { Pattern = App("if", [ Const "false"; Var "then"; Var "else" ])
                  Condition = fun _ -> true
                  Rewrite = Var "else" 
                  Strategy = Outermost }
                
                // Règles is_zero - la spécifique en OUTERMOST, la générale en INNERMOST
                { Pattern = App("is_zero", [ Var "x" ])
                  Condition = fun bindings -> 
                      match bindings |> Map.tryFind "x" with 
                      | Some (Const "0") -> true 
                      | _ -> false
                  Rewrite = Const "true" 
                  Strategy = Outermost }

                { Pattern = App("is_zero", [ Var "y" ])
                  Condition = fun _ -> true
                  Rewrite = Const "false" 
                  Strategy = Innermost }
            ]

        let tree = DiscriminationTree.build rules
        
        let test term =
            printfn "Testing term: %s" (string term)
            let normalized = DiscriminationTree.normalize tree term
            printfn "✅ Normalized to: %s\n" (string normalized)

        // Tests montrant la différence entre innermost et outermost
        
        // Ce terme devrait utiliser la règle outermost pour and[false, ...] 
        // sans évaluer le second argument complexe
        test (App("and", [ Const "false"; App("add", [ App("mul", [ Const "0"; Const "999" ]); Const "1" ]) ]))
        
        // Ce terme devrait d'abord simplifier les arguments avec les règles innermost
        test (App("add", [ App("mul", [ Const "1"; App("add", [ Const "0"; Const "17" ]) ]); Const "0" ]))
        
        // Test avec if - devrait choisir la branche sans évaluer l'autre
        test (App("if", [ Const "true"; Const "42"; App("add", [ Const "999"; Const "999" ]) ]))
        
        test (App("is_zero", [ Const "0" ]))
        test (App("is_zero", [ App("add", [ Const "1"; Const "2" ]) ]))

*)

