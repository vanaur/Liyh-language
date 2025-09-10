namespace Liyh.Utils

module ColorTerm =
    let private esc = "\u001b["

    type public Color =
        | Basic of string           // e.g. "red"
        | Indexed of int            // 0..255
        | Rgb of int * int * int

    let private basicCode (name: string) =
        match name.ToLower() with
        | "black" -> 30
        | "red" -> 31
        | "green" -> 32
        | "yellow" -> 33
        | "blue" -> 34
        | "magenta" -> 35
        | "cyan" -> 36
        | "white" -> 37
        | "bright black" -> 90
        | "bright red" -> 91
        | "bright green" -> 92
        | "bright yellow" -> 93
        | "bright blue" -> 94
        | "bright magenta" -> 95
        | "bright cyan" -> 96
        | "bright white" -> 97
        | _ -> 0

    let private makeCode = function
        | Basic name -> sprintf "%dm" (basicCode name)
        | Indexed i when i >= 0 && i <= 255 -> sprintf "38;5;%dm" i
        | Rgb (r, g, b) -> sprintf "38;2;%d;%d;%dm" r g b
        | _ -> "0m"

    let public colorize (color: Color) (text: string) =
        let code = makeCode color
        $"{esc}{code}{text}{esc}0m"

    let public visibleLength (text: string) =
        let ainsiRegex = System.Text.RegularExpressions.Regex @"\u001b\[[0-9;]*m"
        ainsiRegex.Replace(text, "").Length

