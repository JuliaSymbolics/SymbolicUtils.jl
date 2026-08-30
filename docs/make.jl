using Documenter, DocStringExtensions, SymbolicUtils, TermInterface

include("pages.jl")
DocMeta.setdocmeta!(SymbolicUtils, :DocTestSetup, :(using SymbolicUtils); recursive=true)

makedocs(
    sitename="SymbolicUtils.jl",
    authors="Shashi Gowda",
    clean=true, doctest=true,
    format = Documenter.HTML(#analytics = "UA-90474609-3",
                             assets = ["assets/favicon.ico"],
                             canonical="https://docs.sciml.ai/SymbolicUtils/stable/"),
    pages=pages
    )

deploydocs(
   repo = "github.com/JuliaSymbolics/SymbolicUtils.jl.git";
   push_preview = true
)
