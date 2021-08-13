var coqdocjs_conf = {
    project_page: "https://github.com/ccyip/coq-playground",
    // I prefer ligature
    repl: {
        "forall": "∀",
        "exists": "∃",
        "~": "¬",
        "/\\": "∧",
        "\\/": "∨",
        "<>": "≠",
        "nat": "ℕ",
    },
    // If not ligature, we may pretty print -->! and -->*.
    more_repl: {
        "fun" : "λ",
        // "-->!" : "⟶₁",
        // "-->*" : "⟶★"
    },
    // replInText: ["-->!","-->*"]
    replInText: []
}
