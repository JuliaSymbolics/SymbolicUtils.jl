using Documenter, SymbolicUtils

cp("./docs/Manifest.toml", "./docs/src/assets/Manifest.toml", force = true)
cp("./docs/Project.toml", "./docs/src/assets/Project.toml", force = true)

include("pages.jl")

makedocs(
    sitename="SymbolicUtils.jl",
    authors="Shashi Gowda",
    modules=[SymbolicUtils],
    clean = true,doctest = false, linkcheck = true,
    warnonly = [:docs_block, :missing_docs, :cross_references, :linkcheck],
    format = Documenter.HTML(assets = ["assets/favicon.ico"],
                             canonical="https://docs.sciml.ai/SymbolicUtils/stable/"),
    pages=pages
    )

deploydocs(
   repo = "github.com/JuliaSymbolics/SymbolicUtils.jl.git";
   push_preview = true
)
