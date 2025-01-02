using Documenter, SymbolicUtils

DocMeta.setdocmeta!(
    SymbolicUtils,
    :DocTestSetup,
    :(using SymbolicUtils);
    recursive=true
)

doctest(SymbolicUtils)
